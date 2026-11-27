theory Guest
  imports HolyC Remy.Export
begin

definition codes :: "string \<Rightarrow> integer list" where
  "codes s = map of_char s"

definition decode :: "integer list \<Rightarrow> string" where
  "decode s = map char_of s"

definition compile :: "integer list \<Rightarrow> bool \<times> integer list \<times> integer list" where
  "compile s = (case artifact (decode s) of ((ok,code),report) \<Rightarrow> (ok,codes code,codes report))"

definition tables :: "integer list \<Rightarrow> bool \<times> integer list" where
  "tables s = (case vectors (decode s) of (ok,data) \<Rightarrow> (ok,codes data))"

definition cell :: "integer \<Rightarrow> integer list \<Rightarrow> integer list" where
  "cell x xs = x # xs"

definition empty :: "integer list" where
  "empty = []"

definition first :: "integer list \<Rightarrow> integer" where
  "first xs = hd xs"

definition rest :: "integer list \<Rightarrow> integer list" where
  "rest xs = tl xs"

definition finished :: "integer list \<Rightarrow> bool" where
  "finished xs = List.null xs"

definition status :: "bool \<times> integer list \<times> integer list \<Rightarrow> bool" where
  "status r = fst r"

definition bytes :: "bool \<times> integer list \<times> integer list \<Rightarrow> integer list" where
  "bytes r = fst (snd r)"

definition report :: "bool \<times> integer list \<times> integer list \<Rightarrow> integer list" where
  "report r = snd (snd r)"

definition accepted :: "bool \<times> integer list \<Rightarrow> bool" where
  "accepted r = fst r"

definition rows :: "bool \<times> integer list \<Rightarrow> integer list" where
  "rows r = snd r"

export_code compile tables cell empty first rest finished status bytes report accepted rows
  in HolyC module_name Holy file_prefix holy

end
