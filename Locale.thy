theory Locale
  imports Main match

begin


locale Match =
fixes  empty :: "'t"
fixes insert :: "'a  \<Rightarrow> 't \<Rightarrow> 't"
fixes delete :: "'a \<Rightarrow> 't \<Rightarrow> 't"
fixes lookup :: "'t \<Rightarrow> 'a \<Rightarrow> bool"
fixes  invar :: "'t \<Rightarrow> bool"
fixes  to_set:: "'t \<Rightarrow> 'a set"
fixes  match :: "'t \<Rightarrow> 'a \<Rightarrow> 'a list"

assumes  invar_empty:  "invar empty"
assumes invar_insert: "invar t \<Longrightarrow> invar(insert x t)"
assumes invar_delete: "invar t \<Longrightarrow> invar(delete x t)"
assumes   insert_set:   "to_set (insert x t) = to_set t \<union> {x}"
assumes   delete_set:   "invar t \<Longrightarrow> to_set (delete x t) = to_set t - {x}"
assumes match_correctness: " \<forall>xl\<in>set (match t l). lookup t xl"


interpretation FMPM: Match
where empty = empty_trie and lookup = lookup_trie and insert = insert_trie and delete = delete_trie
and invar = invar_trie and to_set = trie_set and match = FMPM
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add:empty_trie_def)
next
  case (2 t x)
  then show ?case using invar_trie_insert by blast 
next
  case (3 t x)
  then show ?case using lookup_insert' invar_trie_delete by blast 
next
  case (4 x t)
  then show ?case using set_insert by blast 
next
  case (5 t x)
  then show ?case using set_delete by blast 
next
  case (6 t l )
  then show ?case using match_correct by blast 
qed


end