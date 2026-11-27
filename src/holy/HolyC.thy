theory HolyC
  imports Main
begin

ML_file \<open>holyc.ml\<close>

code_printing
  type_constructor bool \<rightharpoonup> (HolyC) "I64"
| constant True \<rightharpoonup> (HolyC) "1"
| constant False \<rightharpoonup> (HolyC) "0"
| constant Not \<rightharpoonup> (HolyC) "HbNot"
| constant HOL.conj \<rightharpoonup> (HolyC) "HbAnd"
| constant HOL.disj \<rightharpoonup> (HolyC) "HbOr"
| constant HOL.implies \<rightharpoonup> (HolyC) "HbImp"
| type_constructor integer \<rightharpoonup> (HolyC) "I64"
| constant "0::integer" \<rightharpoonup> (HolyC) "1"
| constant Code_Numeral.Pos \<rightharpoonup> (HolyC) "HiPos"
| constant Code_Numeral.Neg \<rightharpoonup> (HolyC) "HiNegNum"
| constant "plus :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup> (HolyC) "HiAdd"
| constant "uminus :: integer \<Rightarrow> _" \<rightharpoonup> (HolyC) "HiNeg"
| constant "minus :: integer \<Rightarrow> _" \<rightharpoonup> (HolyC) "HiSub"
| constant Code_Numeral.dup \<rightharpoonup> (HolyC) "HiDup"
| constant Code_Numeral.sub \<rightharpoonup> (HolyC) "HiBad"
| constant "times :: integer \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup> (HolyC) "HiMul"
| constant Code_Numeral.divmod_abs \<rightharpoonup> (HolyC) "HiDivModAbs"
| constant "HOL.equal :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> (HolyC) "HiEq"
| constant "less_eq :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> (HolyC) "HiLe"
| constant "less :: integer \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> (HolyC) "HiLt"
| constant "abs :: integer \<Rightarrow> _" \<rightharpoonup> (HolyC) "HiAbs"
| constant "Bit_Operations.and :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (HolyC) "HiAnd"
| constant "Bit_Operations.or :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (HolyC) "HiOr"
| constant "Bit_Operations.xor :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (HolyC) "HiXor"
| constant "Bit_Operations.not :: integer \<Rightarrow> integer" \<rightharpoonup> (HolyC) "HiNot"
| constant Code_Numeral.push_bit \<rightharpoonup> (HolyC) "HiPush"
| constant Code_Numeral.drop_bit \<rightharpoonup> (HolyC) "HiDrop"

end
