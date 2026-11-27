structure Code_HolyC =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;

infix 4 `$;
infix 4 `$$;
infixr 3 `|=>;

val target = "HolyC";

val conj_name = \<^const_name>\<open>HOL.conj\<close>;
val disj_name = \<^const_name>\<open>HOL.disj\<close>;
val implies_name = \<^const_name>\<open>HOL.implies\<close>;
val pos_name = \<^const_name>\<open>Code_Numeral.Pos\<close>;
val neg_name = \<^const_name>\<open>Code_Numeral.Neg\<close>;
val one_name = \<^const_name>\<open>Num.One\<close>;
val bit0_name = \<^const_name>\<open>Num.Bit0\<close>;
val bit1_name = \<^const_name>\<open>Num.Bit1\<close>;

fun sanitize s =
  let
    val cs = map (fn c => if Symbol.is_ascii_letter c orelse Symbol.is_ascii_digit c then c else "_")
      (Symbol.explode s)
  in implode cs end;

val commas = space_implode ",";

fun decimal k = if k < 0 then "-" ^ string_of_int (~ k) else string_of_int k;

fun limbs 0 = []
  | limbs k = k mod 4294967296 :: limbs (k div 4294967296);

val small_bound = 4611686018427387904;

fun integer_literal k =
  if ~ small_bound <= k andalso k < small_bound then decimal (2 * k + 1)
  else "HiBig(" ^ commas ((if k < 0 then "-1" else "1") :: map decimal (limbs (abs k))) ^ ")";

fun dest_num (IConst {sym = Constant c, ...}) = if c = one_name then SOME 1 else NONE
  | dest_num (IConst {sym = Constant c, ...} `$ t) =
      if c = bit0_name then Option.map (fn k => 2 * k) (dest_num t)
      else if c = bit1_name then Option.map (fn k => 2 * k + 1) (dest_num t)
      else NONE
  | dest_num _ = NONE;

fun dest_literal t =
  (case Code_Thingol.unfold_const_app t of
    SOME ({sym = Constant c, ...}, [n]) =>
      if c = pos_name then dest_num n
      else if c = neg_name then Option.map (fn k => ~ k) (dest_num n)
      else NONE
  | _ => NONE);

fun frees (IConst _) = []
  | frees (IVar NONE) = []
  | frees (IVar (SOME v)) = [v]
  | frees (t1 `$ t2) = union (op =) (frees t2) (frees t1)
  | frees ((v, _) `|=> (body, _)) =
      (case v of SOME v => remove (op =) v | NONE => I) (frees body)
  | frees (ICase {term, clauses, ...}) =
      fold (fn (pat, body) => union (op =)
        (subtract (op =) (Code_Thingol.add_varnames pat []) (frees body))) clauses (frees term);

type builder = {locals: string list Unsynchronized.ref, code: string list Unsynchronized.ref,
  count: int Unsynchronized.ref};

fun builder () : builder =
  {locals = Unsynchronized.ref [], code = Unsynchronized.ref [], count = Unsynchronized.ref 0};

fun fresh_local (b : builder) prefix =
  let
    val n = ! (#count b) + 1;
    val name = prefix ^ string_of_int n;
  in (#count b := n; #locals b := name :: ! (#locals b); name) end;

fun fresh_label (b : builder) =
  let val n = ! (#count b) + 1 in (#count b := n; "L" ^ string_of_int n) end;

fun emit (b : builder) line = #code b := line :: ! (#code b);

fun function_text header (b : builder) =
  let
    val locals = rev (! (#locals b));
    val decl = if null locals then [] else ["I64 " ^ commas locals ^ ";"];
  in cat_lines ([header, "{"] @ decl @ rev (! (#code b)) @ ["}"]) end;

fun serialize ctxt const_syntax module_name program exports =
  let
    val nodes = rev (Code_Symbol.Graph.fold (fn (sym, (stmt, _)) => cons (sym, stmt)) program [])
      |> filter_out (Code_Thingol.is_case o snd)
      |> map (fn (sym, Code_Thingol.Fun ((scheme, eqs), thm)) =>
            (sym, Code_Thingol.Fun ((scheme, filter (snd o snd) eqs), thm))
          | node => node);
    val constructors = fold
      (fn (_, Code_Thingol.Datatype (_, cos)) =>
          fold_index (fn (i, ((co, _), tys)) => Symtab.update (co, (i, length tys, length cos))) cos
        | _ => I) nodes Symtab.empty;
    val classes = fold
      (fn (Type_Class class, Code_Thingol.Class (_, (rels, params))) =>
          Symtab.update (class, (map snd rels, map fst params))
        | _ => I) nodes Symtab.empty;
    val classparams = fold
      (fn (Constant c, Code_Thingol.Classparam class) => Symtab.update (c, class) | _ => I)
      nodes Symtab.empty;
    fun dict_count vs = length (maps snd vs);
    fun fun_arity ((vs, ty), eqs) =
      (case eqs of
        ((ts, _), _) :: _ => length ts
      | [] => length (fst (Code_Thingol.unfold_fun ty)));
    val functions = fold
      (fn (Constant c, Code_Thingol.Fun (scheme_eqs as ((vs, _), _), _)) =>
          Symtab.update (c, (dict_count vs, fun_arity scheme_eqs))
        | _ => I) nodes Symtab.empty;
    fun super_index sub super =
      (case Symtab.lookup classes sub of
        SOME (supers, _) => find_index (fn s => s = super) supers
      | NONE => error ("HolyC: unknown class " ^ quote sub));
    fun param_index class param =
      (case Symtab.lookup classes class of
        SOME (supers, params) => length supers + find_index (fn p => p = param) params
      | NONE => error ("HolyC: unknown class " ^ quote class));

    val used = Unsynchronized.ref Symtab.empty;
    fun fresh_name base =
      let
        val b = sanitize base;
        fun go k =
          let val n = if k = 0 then b else b ^ "_" ^ string_of_int k
          in if Symtab.defined (! used) n then go (k + 1) else (used := Symtab.insert_set n (! used); n) end;
      in go 0 end;
    val names = Unsynchronized.ref Code_Symbol.Table.empty;
    fun name_of sym =
      (case Code_Symbol.Table.lookup (! names) sym of
        SOME n => n
      | NONE =>
          let
            val base = (case sym of
                Class_Instance (tyco, class) => "i_" ^ Long_Name.base_name class ^ "_" ^ Long_Name.base_name tyco
              | Constant c => "h_" ^ Long_Name.base_name c
              | _ => "s_" ^ Code_Symbol.default_base sym);
            val n = fresh_name base;
          in (names := Code_Symbol.Table.update (sym, n) (! names); n) end);
    val _ = List.app (ignore o name_of) exports;

    val globals = Unsynchronized.ref ([] : string list);
    val definitions = Unsynchronized.ref ([] : (string * string) list);
    fun define header text = definitions := (header, text) :: ! definitions;
    val wrappers = Unsynchronized.ref Symtab.empty;
    fun wrapper name call arity =
      let val key = "k_" ^ sanitize name ^ "_" ^ string_of_int arity in
        if Symtab.defined (! wrappers) key then key
        else
          let
            val header = "I64 " ^ key ^ "(I64 *a)";
            val args = map (fn i => "a[" ^ string_of_int i ^ "]") (0 upto arity - 1);
          in
            (wrappers := Symtab.update (key, ()) (! wrappers);
             define header (cat_lines [header, "{", "return " ^ call args ^ ";", "}"]);
             key)
          end
      end;
    val lambdas = Unsynchronized.ref 0;

    fun dict_expr dicts (Dict (rels, plain)) =
          fold_rev (fn (sub, super) => fn e =>
            "HolF(" ^ e ^ "," ^ string_of_int (super_index sub super) ^ ")") rels (plain_expr dicts plain)
    and plain_expr dicts (Dict_Const (inst, dss)) =
          name_of (Class_Instance inst) ^ "(" ^ commas (maps (fn (_, ds) => map (dict_expr dicts) ds) dss) ^ ")"
      | plain_expr dicts (Dict_Var {var, index, ...}) =
          (case AList.lookup (op =) dicts (var, index) of
            SOME n => n
          | NONE => error ("HolyC: unbound dictionary " ^ var));

    fun apply_rest b env dicts e ts =
      fold (fn t => fn acc => "HolAp(" ^ acc ^ "," ^ comp b env dicts t ^ ")") ts e
    and call_named b env dicts (name, closure_name) arity pre ts =
      let val k = length ts in
        if k >= arity then
          let val args = map (comp b env dicts) (take arity ts)
          in apply_rest b env dicts (name ^ "(" ^ commas (pre @ args) ^ ")") (drop arity ts) end
        else
          let
            val args = map (comp b env dicts) ts;
            val total = length pre + arity;
            val code = closure_name total;
            val held = pre @ args;
          in "HolClo(&" ^ code ^ "," ^ string_of_int total ^ (if null held then "" else "," ^ commas held) ^ ")" end
      end
    and comp b env dicts t =
      (case t of
        IVar (SOME v) =>
          (case Symtab.lookup env v of SOME n => n | NONE => error ("HolyC: unbound variable " ^ v))
      | IVar NONE => error "HolyC: wildcard in expression"
      | _ `|=> _ => comp_lambda b env dicts t
      | ICase c => comp_case b env dicts c
      | _ =>
          (case Code_Thingol.unfold_const_app t of
            SOME app => comp_app b env dicts app
          | NONE =>
              let val (f, ts) = Code_Thingol.unfold_app t
              in apply_rest b env dicts (comp b env dicts f) ts end))
    and lazy b env dicts guard a c rest =
      let
        val r = fresh_local b "t";
        val _ = emit b (r ^ "=" ^ comp b env dicts a ^ ";");
        val _ = emit b ("if (" ^ guard r ^ ") {");
        val _ = emit b (r ^ "=" ^ comp b env dicts c ^ ";");
        val _ = emit b "}";
      in apply_rest b env dicts r rest end
    and comp_app b env dicts (const as {sym, dictss, ...}, ts) =
      (case sym of
        Constant c =>
          if c = conj_name andalso length ts >= 2 then
            lazy b env dicts I (nth ts 0) (nth ts 1) (drop 2 ts)
          else if c = disj_name andalso length ts >= 2 then
            lazy b env dicts (fn r => "!" ^ r) (nth ts 0) (nth ts 1) (drop 2 ts)
          else if c = implies_name andalso length ts >= 2 then
            let
              val r = fresh_local b "t";
              val _ = emit b (r ^ "=" ^ comp b env dicts (nth ts 0) ^ ";");
              val _ = emit b ("if (" ^ r ^ ") {");
              val _ = emit b (r ^ "=" ^ comp b env dicts (nth ts 1) ^ ";");
              val _ = emit b "} else {";
              val _ = emit b (r ^ "=1;");
              val _ = emit b "}";
            in apply_rest b env dicts r (drop 2 ts) end
          else
            (case dest_literal (IConst const `$$ ts) of
              SOME k => integer_literal k
            | NONE =>
              (case const_syntax c of
                SOME (n, Code_Printer.Plain_printer s) =>
                  if n = 0 then apply_rest b env dicts s ts
                  else call_named b env dicts (s, fn total =>
                    wrapper s (fn args => s ^ "(" ^ commas args ^ ")") total) n [] ts
              | SOME _ => error ("HolyC: complex syntax for " ^ quote c)
              | NONE =>
                (case Symtab.lookup constructors c of
                  SOME (tag, arity, _) =>
                    if arity = 0 then apply_rest b env dicts (string_of_int tag) ts
                    else call_named b env dicts ("HolCon", fn total =>
                      wrapper "HolCon" (fn args => "HolCon(" ^ commas args ^ ")") total) arity
                      [string_of_int tag] ts
                | NONE =>
                  (case Symtab.lookup classparams c of
                    SOME class =>
                      let val d = (case flat dictss of [d] => dict_expr dicts d
                        | _ => error ("HolyC: class parameter without dictionary " ^ quote c))
                      in apply_rest b env dicts
                        ("HolF(" ^ d ^ "," ^ string_of_int (param_index class c) ^ ")") ts end
                  | NONE =>
                    (case Symtab.lookup functions c of
                      SOME (_, arity) =>
                        let
                          val name = name_of sym;
                          val pre = maps (map (dict_expr dicts)) dictss;
                        in call_named b env dicts (name, fn total =>
                          wrapper name (fn args => name ^ "(" ^ commas args ^ ")") total) arity pre ts end
                    | NONE => error ("HolyC: no code for " ^ quote c))))))
      | _ => error "HolyC: unexpected symbol in application")
    and comp_lambda b env dicts t =
      let
        val (params, body) = Code_Thingol.unfold_abs t;
        val captured = filter (Symtab.defined env) (frees t);
        val n = ! lambdas + 1;
        val _ = lambdas := n;
        val name = "l_" ^ string_of_int n;
        val inner = builder ();
        val ncap = length captured + length dicts;
        fun arg i = "a[" ^ string_of_int i ^ "]";
        val (env', i) = fold (fn v => fn (e, i) =>
          let val x = fresh_local inner "v" in (emit inner (x ^ "=" ^ arg i ^ ";"); (Symtab.update (v, x) e, i + 1)) end)
          captured (Symtab.empty, 0);
        val (dicts', i) = fold (fn (key, _) => fn (ds, i) =>
          let val x = fresh_local inner "d" in (emit inner (x ^ "=" ^ arg i ^ ";"); (ds @ [(key, x)], i + 1)) end)
          dicts ([], i);
        val (env'', _) = fold (fn (v, _) => fn (e, i) =>
          (case v of
            SOME v => let val x = fresh_local inner "v" in (emit inner (x ^ "=" ^ arg i ^ ";"); (Symtab.update (v, x) e, i + 1)) end
          | NONE => (e, i + 1))) params (env', i);
        val result = comp inner env'' dicts' body;
        val _ = emit inner ("return " ^ result ^ ";");
        val header = "I64 " ^ name ^ "(I64 *a)";
        val _ = define header (function_text header inner);
        val held = map (the o Symtab.lookup env) captured @ map snd dicts;
      in
        "HolClo(&" ^ name ^ "," ^ string_of_int (ncap + length params) ^
          (if null held then "" else "," ^ commas held) ^ ")"
      end
    and match b env scrutinee pat fail =
      (case pat of
        IVar NONE => env
      | IVar (SOME v) => Symtab.update (v, scrutinee) env
      | _ =>
        (case dest_literal pat of
          SOME k => (emit b ("if (!HiEq(" ^ scrutinee ^ "," ^ integer_literal k ^ ")) goto " ^ fail ^ ";"); env)
        | NONE =>
          (case Code_Thingol.unfold_const_app pat of
            SOME ({sym = Constant c, ...}, ps) =>
              (case const_syntax c of
                SOME (_, Code_Printer.Plain_printer s) =>
                  if null ps then (emit b ("if (" ^ scrutinee ^ "!=" ^ s ^ ") goto " ^ fail ^ ";"); env)
                  else error ("HolyC: pattern with arguments on target constant " ^ quote c)
              | SOME _ => error ("HolyC: complex syntax in pattern " ^ quote c)
              | NONE =>
                (case Symtab.lookup constructors c of
                  SOME (tag, _, count) =>
                    let
                      val _ = if count > 1 then
                        emit b ("if (HolTag(" ^ scrutinee ^ ")!=" ^ string_of_int tag ^ ") goto " ^ fail ^ ";")
                        else ();
                    in
                      fold_index (fn (i, p) => fn env =>
                        let val field = "HolF(" ^ scrutinee ^ "," ^ string_of_int (i + 1) ^ ")" in
                          (case p of
                            IVar NONE => env
                          | _ =>
                            let val x = fresh_local b "t"
                            in (emit b (x ^ "=" ^ field ^ ";"); match b env x p fail) end)
                        end) ps env
                    end
                | NONE => error ("HolyC: non-constructor pattern " ^ quote c)))
          | _ => error "HolyC: unsupported pattern")))
    and comp_case b env dicts {term, clauses, ...} =
      let
        val s = fresh_local b "t";
        val _ = emit b (s ^ "=" ^ comp b env dicts term ^ ";");
        val r = fresh_local b "t";
        val finish = fresh_label b;
        val _ = List.app (fn (pat, body) =>
          let
            val next = fresh_label b;
            val env' = match b env s pat next;
            val _ = emit b (r ^ "=" ^ comp b env' dicts body ^ ";");
            val _ = emit b ("goto " ^ finish ^ ";");
          in emit b (next ^ ":;") end) clauses;
        val _ = emit b "throw('Match');";
        val _ = emit b (finish ^ ":;");
      in r end;

    fun dict_params vs =
      flat (map_index (fn (i, (v, sort)) =>
        map_index (fn (j, _) => ((v, j), "d" ^ string_of_int i ^ "_" ^ string_of_int j)) sort) vs);

    fun emit_function sym ((vs, ty), eqs) =
      let
        val name = name_of sym;
        val dicts = dict_params vs;
        val arity = fun_arity ((vs, ty), eqs);
        val params = map (fn i => "p" ^ string_of_int i) (0 upto arity - 1);
        val memo = null dicts andalso arity = 0;
        val body_name = if memo then "m" ^ name else name;
        val header = "I64 " ^ body_name ^ "(" ^ commas (map (fn n => "I64 " ^ n) (map snd dicts @ params)) ^ ")";
        val b = builder ();
        val _ = List.app (fn ((ts, rhs), _) =>
          let
            val next = fresh_label b;
            val env = fold (fn (p, t) => fn env => match b env p t next) (params ~~ ts) Symtab.empty;
            val _ = emit b ("return " ^ comp b env dicts rhs ^ ";");
          in emit b (next ^ ":;") end) eqs;
        val _ = emit b "throw('Match');";
        val _ = define header (function_text header b);
      in
        if memo then
          let
            val g = "g" ^ name;
            val f = "f" ^ name;
            val outer = "I64 " ^ name ^ "()";
          in
            (globals := ("I64 " ^ g ^ "=0," ^ f ^ "=0;") :: ! globals;
             define outer (cat_lines [outer, "{", "I64 r;", "if (" ^ f ^ ") return " ^ g ^ ";",
               "HolPermOn();", "r=" ^ body_name ^ "();", g ^ "=r;", f ^ "=1;", "HolPermOff();",
               "return r;", "}"]))
          end
        else ()
      end;

    fun emit_instance sym {class, tyco, vs, superinsts, inst_params, ...} =
      let
        val name = name_of sym;
        val dicts = dict_params vs;
        val (supers, params) = the (Symtab.lookup classes class);
        val size = length supers + length params;
        val header = "I64 " ^ name ^ "(" ^ commas (map (fn n => "I64 " ^ n) (map snd dicts)) ^ ")";
        val b = builder ();
        val r = fresh_local b "t";
        val memo = null dicts;
        val g = "g" ^ name;
        val f = "f" ^ name;
        val _ = if memo then
          (globals := ("I64 " ^ g ^ "=0," ^ f ^ "=0;") :: ! globals;
           emit b ("if (" ^ f ^ ") return " ^ g ^ ";");
           emit b "HolPermOn();";
           emit b (r ^ "=HolRec(" ^ string_of_int size ^ ");");
           emit b (g ^ "=" ^ r ^ ";");
           emit b (f ^ "=1;"))
          else emit b (r ^ "=HolRec(" ^ string_of_int size ^ ");");
        val _ = List.app (fn (super, x) =>
          emit b ("HolSet(" ^ r ^ "," ^ string_of_int (super_index class super) ^ "," ^
            dict_expr dicts (Dict ([], Dict_Const ((tyco, super), x))) ^ ");")) superinsts;
        val _ = List.app (fn ((param, (const, _)), _) =>
          emit b ("HolSet(" ^ r ^ "," ^ string_of_int (param_index class param) ^ "," ^
            comp_app b Symtab.empty dicts (const, []) ^ ");")) inst_params;
        val _ = if memo then emit b "HolPermOff();" else ();
        val _ = emit b ("return " ^ r ^ ";");
      in define header (function_text header b) end;

    val _ = List.app
      (fn (sym, Code_Thingol.Fun (scheme_eqs, _)) => emit_function sym scheme_eqs
        | (sym, Code_Thingol.Classinst inst) => emit_instance sym inst
        | _ => ()) nodes;

    val _ = (case (Symtab.lookup constructors one_name, Symtab.lookup constructors bit0_name) of
        (SOME (one, _, _), SOME (bit0, _, _)) =>
          (define "I64 HiPos(I64 n)" (cat_lines ["I64 HiPos(I64 n)", "{", "I64 t=HolTag(n);",
             "if (t==" ^ string_of_int one ^ ") return 3;",
             "if (t==" ^ string_of_int bit0 ^ ") return HiDup(HiPos(HolF(n,1)));",
             "return HiAdd(HiDup(HiPos(HolF(n,1))),3);", "}"]);
           define "I64 HiNegNum(I64 n)" (cat_lines ["I64 HiNegNum(I64 n)", "{", "return HiNeg(HiPos(n));", "}"]))
      | _ => ());
    val defs = rev (! definitions);
    val text = cat_lines (rev (! globals) @ map (fn (s, _) => "extern " ^ s ^ ";") defs @ map snd defs);
    fun deresolve sym = Code_Symbol.Table.lookup (! names) sym;
  in
    (Code_Target.Singleton ("HC", Pretty.str text), deresolve)
  end;

val serializer : Code_Target.serializer =
  fn _ => fn ctxt => fn {const_syntax, module_name, ...} => fn program => fn exports =>
    serialize ctxt const_syntax module_name program exports;

val literals = Code_Printer.Literals {
  literal_string = fn _ => error "HolyC: string literals are not supported",
  literal_numeral = integer_literal,
  literal_list = fn _ => error "HolyC: list literals are not supported",
  infix_cons = (6, "")};

val _ = Theory.setup
  (Code_Target.add_language
    (target, {serializer = serializer, literals = literals,
      check = {env_var = "", make_destination = I,
        run_command = Code_Target.run_command_bash (K "true")},
      evaluation_args = []}));

end;
