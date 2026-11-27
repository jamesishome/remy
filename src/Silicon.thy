theory Silicon
  imports Frontend
begin

lemma integer_bound: "list_all (\<lambda>b. b < 256) xs \<Longrightarrow> integer xs < 256 ^ length xs"
  by (induction xs) auto

lemma octets_integer:
  "length xs = k \<Longrightarrow> list_all (\<lambda>b. b < 256) xs \<Longrightarrow> octets k (integer xs) = xs"
  by (induction xs arbitrary: k) auto

lemma octets_mod: "octets k (n mod 256 ^ k) = octets k n"
proof (induction k arbitrary: n)
  case (Suc k)
  have "n mod (256 * 256 ^ k) = 256 * (n div 256 mod 256 ^ k) + n mod 256"
    by (simp add: mod_mult2_eq)
  then have "n mod 256 ^ Suc k div 256 = n div 256 mod 256 ^ k" "n mod 256 ^ Suc k mod 256 = n mod 256"
    by simp_all
  then show ?case using Suc by simp
qed simp

lemma extend32_low: "n < 2 ^ 32 \<Longrightarrow> unat (extend32 n) mod 2 ^ 32 = n"
proof -
  assume small: "n < 2 ^ 32"
  let ?z = "signed_take_bit 31 (int n)"
  have "unat (extend32 n) = nat (?z mod 2 ^ 64)"
    by (simp add: extend32_def unat_eq_nat_uint uint_word_of_int)
  then have "unat (extend32 n) mod 2 ^ 32 = nat (?z mod 2 ^ 64 mod 2 ^ 32)"
    by (simp add: nat_mod_distrib)
  also have "?z mod 2 ^ 64 mod 2 ^ 32 = ?z mod 2 ^ 32"
    by (rule mod_mod_cancel) (simp add: le_imp_power_dvd)
  also have "?z mod 2 ^ 32 = int n"
    using small take_bit_signed_take_bit[of 32 31 "int n"] by (simp add: take_bit_eq_mod)
  finally show ?thesis by simp
qed

lemma octets_extend32:
  "length xs = 4 \<Longrightarrow> list_all (\<lambda>b. b < 256) xs \<Longrightarrow> octets 4 (unat (extend32 (integer xs))) = xs"
proof -
  assume size: "length xs = 4" and bytes: "list_all (\<lambda>b. b < 256) xs"
  have small: "integer xs < 2 ^ 32" using integer_bound[OF bytes] size by simp
  have "octets 4 (unat (extend32 (integer xs))) = octets 4 (unat (extend32 (integer xs)) mod 256 ^ 4)"
    by (simp only: octets_mod)
  also have "\<dots> = octets 4 (integer xs)" using extend32_low[OF small] by simp
  finally show ?thesis using octets_integer[OF size bytes] by simp
qed

lemma take_drop_split:
  "k + m \<le> length bs \<Longrightarrow> bs = take k bs @ take m (drop k bs) @ drop (k + m) bs"
  by (metis append.assoc append_take_drop_id drop_drop add.commute take_add)

lemma fixed64_decode:
  "List.find (\<lambda>i. take (length (microbytes i)) bs = microbytes i) fixed64 = Some i \<Longrightarrow>
    bs = microbytes i @ drop (length (microbytes i)) bs"
  by (auto simp: find_Some_iff) (metis append_take_drop_id)

theorem decode64_sound:
  assumes decoded: "decode64 bs = Some (i,rest)" and bytes: "list_all (\<lambda>b. b < 256) bs"
  shows "bs = microbytes i @ rest"
proof -
  have sub: "list_all (\<lambda>b. b < 256) (take m (drop k bs))" for k m
    using bytes by (auto simp: list_all_iff dest: in_set_takeD in_set_dropD)
  consider (imm64) "take 2 bs = [72,184]"
    | (imm32) "take 2 bs \<noteq> [72,184]" "take 3 bs = [72,199,192]"
    | (short) "take 2 bs \<noteq> [72,184]" "take 3 bs \<noteq> [72,199,192]" "take 4 bs = [72,139,68,36]"
    | (long) "take 2 bs \<noteq> [72,184]" "take 3 bs \<noteq> [72,199,192]" "take 4 bs \<noteq> [72,139,68,36]"
        "take 4 bs = [72,139,132,36]"
    | (table) "take 2 bs \<noteq> [72,184]" "take 3 bs \<noteq> [72,199,192]" "take 4 bs \<noteq> [72,139,68,36]"
        "take 4 bs \<noteq> [72,139,132,36]"
    by blast
  then show ?thesis
  proof cases
    case imm64
    let ?xs = "take 8 (drop 2 bs)"
    have facts: "10 \<le> length bs" "i = Imm64 (word_of_nat (integer ?xs))" "rest = drop 10 bs"
      using decoded imm64 by (auto simp: decode64_def split: if_splits)
    have size: "length ?xs = 8" using facts by simp
    have small: "integer ?xs < 2 ^ 64" using integer_bound[OF sub[of 8 2]] size by simp
    have "octets 8 (unat (word_of_nat (integer ?xs) :: pixel)) = ?xs"
      using small octets_integer[OF size sub[of 8 2]] by (simp add: unat_of_nat)
    then show ?thesis
      using facts imm64 take_drop_split[of 2 8 bs] by simp
  next
    case imm32
    let ?xs = "take 4 (drop 3 bs)"
    have facts: "7 \<le> length bs" "i = Imm32 (extend32 (integer ?xs))" "rest = drop 7 bs"
      using decoded imm32 by (auto simp: decode64_def split: if_splits)
    have size: "length ?xs = 4" using facts by simp
    show ?thesis
      using facts imm32 take_drop_split[of 3 4 bs] octets_extend32[OF size sub[of 4 3]] by simp
  next
    case short
    let ?n = "integer (take 1 (drop 4 bs))"
    have facts: "5 \<le> length bs" "?n < 128" "?n mod 8 = 0" "i = Load (?n div 8)" "rest = drop 5 bs"
      using decoded short by (auto simp: decode64_def Let_def split: if_splits)
    have one: "take 1 (drop 4 bs) = [bs ! 4]"
      using facts(1) by (simp add: take_Suc_conv_app_nth)
    have whole: "8 * (?n div 8) = ?n" using facts(3) by (metis add.right_neutral mult_div_mod_eq)
    have exact: "8 * (?n div 8) = bs ! 4" using whole one by simp
    have "bs = take 4 bs @ take 1 (drop 4 bs) @ drop 5 bs"
      using take_drop_split[of 4 1 bs] facts(1) by simp
    then show ?thesis using facts short exact one by simp
  next
    case long
    let ?xs = "take 4 (drop 4 bs)"
    let ?n = "integer ?xs"
    have facts: "8 \<le> length bs" "?n mod 8 = 0" "16 \<le> ?n div 8" "i = Load (?n div 8)" "rest = drop 8 bs"
      using decoded long by (auto simp: decode64_def Let_def split: if_splits)
    have size: "length ?xs = 4" using facts by simp
    have exact: "8 * (?n div 8) = ?n" using facts(2) by (metis add.right_neutral mult_div_mod_eq)
    have "microbytes i = [72,139,132,36] @ ?xs"
      using facts(3,4) exact octets_integer[OF size sub[of 4 4]] by simp
    then show ?thesis using facts long take_drop_split[of 4 4 bs] by simp
  next
    case table
    obtain j where j: "List.find (\<lambda>i. take (length (microbytes i)) bs = microbytes i) fixed64 = Some j"
      "i = j" "rest = drop (length (microbytes j)) bs"
      using decoded table by (auto simp: decode64_def Let_def split: if_splits)
    show ?thesis using fixed64_decode[OF j(1)] j by simp
  qed
qed

lemma bytes_drop: "list_all (\<lambda>b. b < 256) bs \<Longrightarrow> list_all (\<lambda>b. b < 256) (drop k bs)"
  by (auto simp: list_all_iff dest: in_set_dropD)

lemma split_return:
  assumes "drop n tail = body @ [195]"
  shows "\<exists>front. tail = front @ [195] \<and> n \<le> length front \<and> drop n front = body"
proof -
  have n: "n < length tail" using assms by (metis append_is_Nil_conv drop_all not_less not_Cons_self2)
  have "tail = take n tail @ body @ [195]" using assms append_take_drop_id[of n tail] by metis
  then show ?thesis using n
    by (intro exI[where x="take n tail @ body"]) (auto simp: min_def)
qed

lemma simulate64_frames:
  "simulate64 fuel bytes c = Some (address,d) \<Longrightarrow> list_all (\<lambda>b. b < 256) bytes \<Longrightarrow>
    \<exists>body q. bytes = body @ [195] \<and> executes64 body c q \<and> ret64 q = Some (address,d)"
proof (induction fuel arbitrary: bytes c)
  case 0
  then show ?case by (simp add: simulate64.simps)
next
  case (Suc fuel)
  note run = Suc.prems(1) and bytes = Suc.prems(2)
  have sub: "list_all (\<lambda>b. b < 256) (take m (drop k bytes))" for k m
    using bytes by (auto simp: list_all_iff dest: in_set_takeD in_set_dropD)
  consider (ret) "bytes = [195]"
    | (jump) "bytes \<noteq> []" "bytes \<noteq> [195]" "take 1 bytes = [233]"
    | (branch) "bytes \<noteq> []" "bytes \<noteq> [195]" "take 1 bytes \<noteq> [233]" "take 2 bytes = [15,132]"
    | (step) "bytes \<noteq> []" "bytes \<noteq> [195]" "take 1 bytes \<noteq> [233]" "take 2 bytes \<noteq> [15,132]"
    using run by (cases "bytes = []") (auto simp: simulate64.simps)
  then show ?case
  proof cases
    case ret
    then show ?thesis using run
      by (intro exI[where x="[]"] exI[where x=c]) (auto simp: simulate64.simps intro: executes64.empty)
  next
    case jump
    let ?xs = "take 4 (drop 1 bytes)"
    let ?n = "integer ?xs"
    have facts: "5 \<le> length bytes" "?n < 2 ^ 31" "?n \<le> length bytes - 5"
      "simulate64 fuel (drop (5 + ?n) bytes) c = Some (address,d)"
      using run jump by (auto simp: simulate64.simps Let_def split: if_splits)
    obtain body q where inner: "drop (5 + ?n) bytes = body @ [195]"
      "executes64 body c q" "ret64 q = Some (address,d)"
      using Suc.IH[OF facts(4) bytes_drop[OF bytes]] by blast
    have shape: "bytes = [233] @ ?xs @ drop 5 bytes"
      using jump facts(1) take_drop_split[of 1 4 bytes] by simp
    obtain front where front: "drop 5 bytes = front @ [195]" "?n \<le> length front" "drop ?n front = body"
      using split_return[of ?n "drop 5 bytes" body] inner(1) by (auto simp: add.commute)
    have size: "length ?xs = 4" using facts(1) by simp
    have "executes64 ([233] @ octets 4 ?n @ front) c q"
      using facts(2) front(2,3) inner(2) by (intro executes64.jump) auto
    then have "executes64 ([233] @ ?xs @ front) c q"
      using octets_integer[OF size sub[of 4 1]] by simp
    then show ?thesis
      using shape front(1) inner(3) by (intro exI[where x="[233] @ ?xs @ front"]) auto
  next
    case branch
    let ?xs = "take 4 (drop 2 bytes)"
    let ?n = "integer ?xs"
    obtain flag where facts: "6 \<le> length bytes" "?n < 2 ^ 31" "?n \<le> length bytes - 6"
      "zero64 c = Some flag"
      "simulate64 fuel (drop (6 + (if flag then ?n else 0)) bytes) c = Some (address,d)"
      using run branch by (auto simp: simulate64.simps Let_def split: if_splits option.splits)
    have size: "length ?xs = 4" using facts(1) by simp
    have shape: "bytes = [15,132] @ ?xs @ drop 6 bytes"
      using branch facts(1) take_drop_split[of 2 4 bytes] by simp
    have code: "octets 4 ?n = ?xs" using octets_integer[OF size sub[of 4 2]] .
    show ?thesis
    proof (cases flag)
      case True
      have taken: "simulate64 fuel (drop (6 + ?n) bytes) c = Some (address,d)" using facts(5) True by simp
      obtain body q where inner: "drop (6 + ?n) bytes = body @ [195]"
        "executes64 body c q" "ret64 q = Some (address,d)"
        using Suc.IH[OF taken bytes_drop[OF bytes]] by blast
      obtain front where front: "drop 6 bytes = front @ [195]" "?n \<le> length front" "drop ?n front = body"
        using split_return[of ?n "drop 6 bytes" body] inner(1) by (auto simp: add.commute)
      have "executes64 ([15,132] @ octets 4 ?n @ front) c q"
        using facts(2,4) True front(2,3) inner(2) by (intro executes64.zero) auto
      then show ?thesis using shape front(1) inner(3) code
        by (intro exI[where x="[15,132] @ ?xs @ front"]) auto
    next
      case False
      have taken: "simulate64 fuel (drop 6 bytes) c = Some (address,d)" using facts(5) False by simp
      obtain body q where inner: "drop 6 bytes = body @ [195]"
        "executes64 body c q" "ret64 q = Some (address,d)"
        using Suc.IH[OF taken bytes_drop[OF bytes]] by blast
      have "executes64 ([15,132] @ octets 4 ?n @ body) c q"
        using facts(2,4) False inner(2) by (intro executes64.nonzero) auto
      then show ?thesis using shape inner(1,3) code
        by (intro exI[where x="[15,132] @ ?xs @ body"]) auto
    qed
  next
    case step
    obtain i rest c' where facts: "decode64 bytes = Some (i,rest)" "microvalid i"
      "microstep i c = Some c'" "simulate64 fuel rest c' = Some (address,d)"
      using run step by (auto simp: simulate64.simps split: if_splits bind_splits option.splits)
    have shape: "bytes = microbytes i @ rest" using decode64_sound[OF facts(1) bytes] .
    have rest_bytes: "list_all (\<lambda>b. b < 256) rest"
      using bytes shape by simp
    obtain body q where inner: "rest = body @ [195]" "executes64 body c' q"
      "ret64 q = Some (address,d)"
      using Suc.IH[OF facts(4) rest_bytes] by blast
    have "executes64 (microbytes i @ body) c q"
      using facts(2,3) inner(2) by (rule executes64.advance)
    then show ?thesis using shape inner(1,3)
      by (intro exI[where x="microbytes i @ body"]) auto
  qed
qed

theorem simulate64_sound:
  "simulate64 fuel bytes c = Some (address,d) \<Longrightarrow> list_all (\<lambda>b. b < 256) bytes \<Longrightarrow>
    returns64 bytes c address d"
  unfolding returns64_def by (drule simulate64_frames) auto

fun slot :: "register \<Rightarrow> nat" where
  "slot Rax = 0" | "slot Rcx = 1" | "slot Rbx = 2" | "slot Rdx = 3" | "slot R8 = 4" | "slot R9 = 5"

definition word_at :: "nat \<Rightarrow> nat list \<Rightarrow> pixel" where
  "word_at k bs = word_of_nat (integer (take 8 (drop k bs)))"

definition flag_of :: "nat \<Rightarrow> bool option" where
  "flag_of n = (if n = 0 then Some False else if n = 1 then Some True else None)"

definition flag_code :: "bool option \<Rightarrow> nat" where
  "flag_code f = (case f of Some False \<Rightarrow> 0 | Some True \<Rightarrow> 1 | None \<Rightarrow> 2)"

definition state_of :: "nat list \<Rightarrow> processor" where
  "state_of bs = \<lparr>state64 = \<lparr>registers = (\<lambda>r. word_at (8 * slot r) bs),
      stack = map (\<lambda>i. word_at (58 + 8 * i) bs) [0..<bs ! 57]\<rparr>,
    pointer64 = word_at 48 bs, zero64 = flag_of (bs ! 56 mod 4), carry64 = flag_of (bs ! 56 div 4)\<rparr>"

definition state_bytes :: "processor \<Rightarrow> nat list" where
  "state_bytes c = concat (map (\<lambda>r. octets 8 (unat (registers (state64 c) r))) [Rax,Rcx,Rbx,Rdx,R8,R9]) @
    octets 8 (unat (pointer64 c)) @ [flag_code (zero64 c) + 4 * flag_code (carry64 c)] @
    octets 2 (length (stack (state64 c))) @ concat (map (\<lambda>v. octets 8 (unat v)) (stack (state64 c)))"

fun replay_cases :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "replay_cases 0 bs = []"
| "replay_cases (Suc fuel) bs = (if length bs < 58 then [] else
    let header = 58 + 8 * (bs ! 57); size = integer (take 2 (drop header bs));
      code = take size (drop (header + 2) bs) in
    (case simulate64 (Suc size) code (state_of bs) of None \<Rightarrow> [0]
      | Some (address,c) \<Rightarrow> 1 # octets 8 (unat address) @ state_bytes c) @
      replay_cases fuel (drop (header + 2 + size) bs))"

definition replay :: "string \<Rightarrow> bool \<times> string" where
  "replay s = (True, map char_of_nat (replay_cases (length s) (map nat_of_char s)))"

end
