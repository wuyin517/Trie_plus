theory match
  imports Main Trie_plus
begin


(***chinese/english ***)
datatype ch = English nat | Chinese nat nat

(*** 中文 为人民服务  ***)
definition "list1 = [Chinese 206 170,Chinese 200 203,Chinese 195 241,Chinese 183 254,Chinese 206 241]"
(*** 中文 人民日报  ***)
definition "list2 = [Chinese 200 203,Chinese 195 241,Chinese 200 213,Chinese 177 168]"
(*** 中文 服务社会  ***)
definition "list3 = [Chinese 183 254,Chinese 206 241,Chinese 201 231,Chinese 187 225]"
(***英文 love  ***)
definition "list4 = [English 108, English 111, English 118, English 101]"
(*** 中文 人民  ***)
definition "list5 = [Chinese 200 203,Chinese 195 241]"

definition "list6 = []"
(**只包含list1 list2 list3 list5**)
definition "trie = Trie_plus False
  [(Chinese 206 170,
    Trie_plus False
     [(Chinese 200 203,
       Trie_plus False
        [(Chinese 195 241,
          Trie_plus False
           [(Chinese 183 254, Trie_plus False [(Chinese 206 241, Trie_plus True [])])])])]),
   (Chinese 200 203,
    Trie_plus False
     [(Chinese 195 241,
       Trie_plus True [(Chinese 200 213, Trie_plus False [(Chinese 177 168, Trie_plus True [])])])]),
   (Chinese 183 254,
    Trie_plus False
     [(Chinese 206 241,
       Trie_plus False
        [(Chinese 201 231, Trie_plus False [(Chinese 187 225, Trie_plus True [])])])])]"

value trie

fun look_up::"ch trie \<Rightarrow> ch list \<Rightarrow> ch list" where
"look_up (Trie_plus b m) [] = []"|
"look_up (Trie_plus b m) (x#xs) = (case map_of m x of
      None \<Rightarrow> [] |
      Some st \<Rightarrow> (x # look_up st xs))"

fun prefix_lookup ::  "ch trie \<Rightarrow> ch list \<Rightarrow> ch list" where
"prefix_lookup t ks =(let l = (look_up t ks) in (if (lookup_trie t l) then l else []))"


fun FMPM::"ch trie \<Rightarrow>ch list \<Rightarrow> ch list list" where
"FMPM (Trie_plus b m) [] = []"|
"FMPM (Trie_plus b m) (x#xs) = (case prefix_lookup (Trie_plus b m) (x#xs) of [] \<Rightarrow>
                                 FMPM (Trie_plus b m) xs | sx \<Rightarrow> sx # FMPM (Trie_plus b m) xs)"


(*** proof ****)
fun startsWith :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "startsWith [] ys = True" |
        "startsWith (x # xs) [] = False" |
        "startsWith (x # xs) (y # ys) = (if x = y then startsWith xs ys else False)"
value "startsWith  ''ab'' ''abcde''"

(*** 字串 ***)


value "look_up trie [Chinese 206 170, Chinese 200 203, Chinese 196 241, Chinese 183 254, Chinese 205 241]"

lemma look_up_empty:"look_up t [] = []" 
  apply (induct t)
  by auto

lemma look_up_empty':"look_up empty_trie l = []"
  apply(cases l)
   apply simp_all
  using look_up_empty apply auto[1]
  by (simp add: empty_trie_def) 


lemma look_up_cases:"l\<noteq> [] \<Longrightarrow> look_up (Trie_plus b m) l = (case map_of m (hd l) of None \<Rightarrow> []| Some st \<Rightarrow> ((hd l) # look_up st (tl l) ) )"
  apply (induct l)
   apply (auto split:option.split)
  done 


lemma ll5:"startsWith xs ys \<Longrightarrow> startsWith (a#xs) (a#ys)"
  by(induct xs ys rule:startsWith.induct) auto

lemma look_up_pre:"startsWith (look_up (Trie_plus b m) l) l"
proof(induct l rule:look_up.induct)
  case (1 b m)
  then show ?case by simp
next
  case (2 b m x xs)
  then show ?case 
  proof(cases "map_of m x")
    case None
    then show ?thesis by (simp add:look_up_cases)
  next
    case (Some at)
    then show ?thesis using 2[of at] 
      by simp
  qed
qed

lemma ll7:"lookup_trie t l \<Longrightarrow> look_up t l = l"
  proof(induct t l rule: lookup_trie.induct)
    case (1 b m)
    then show ?case by simp
  next
    case (2 b m k ks)
    then show ?case 
    proof(cases "map_of m k")
      case None
      then show ?thesis using 2 by simp
    next
      case (Some st)
      then show ?thesis using 2 
        by simp 
  qed
qed



(***------- 普通匹配  -----***)
lemma prefix_lookup_nil:"\<not>(lookup_trie t (look_up t ks))  \<Longrightarrow> prefix_lookup t ks = [] "
  by auto

lemma prefix_lookup_conv:"(lookup_trie t (look_up t ks))  \<Longrightarrow> prefix_lookup t ks = (look_up t ks) "
  by auto

value "prefix_lookup trie [Chinese 206 170, Chinese 200 203, Chinese 196 241, Chinese 183 254, Chinese 205 241]"

lemma prefix_lookup_eq:"lookup_trie t l \<Longrightarrow> prefix_lookup t l = l" 
  proof(induct t l rule: lookup_trie.induct)
    case (1 b m)
    then show ?case by simp
  next
    case (2 b m k ks)
    then show ?case 
    proof(cases "map_of m k")
      case None
      then show ?thesis using 2 by simp
    next
      case (Some st)
      then show ?thesis using 2 
        by (simp add: ll7)        
  qed
qed

lemma lll3:"prefix_lookup t l = str \<Longrightarrow> startsWith str l "
proof(induct t )
  case (Trie_plus b kvs)
  then show ?case 
    by (metis look_up_pre prefix_lookup_nil prefix_lookup_conv startsWith.simps(1))
qed


lemma l0:"FMPM t [] = []"
  apply(induct t)
  by auto
lemma FMPM_emoty:"FMPM empty_trie l = []"
  apply(induct l)
  using l0 apply blast
  by (simp add: empty_trie_def)


lemma prefix_lookup_lookup_trie:"prefix_lookup t l \<noteq> [] \<Longrightarrow> lookup_trie t (prefix_lookup t l)"
  by (metis prefix_lookup_conv prefix_lookup_nil)

lemma FMPM_lookup_trie:"FMPM t l \<noteq> [] \<Longrightarrow>lookup_trie t l \<Longrightarrow> hd(FMPM t l) = l "
proof(induction t l rule:FMPM.induct)
  case (1 b m)
  then show ?case 
    by simp
next
  case (2 b m x xs)
  then show ?case 
    by (metis list.sel(1) list.simps(5) prefix_lookup_eq FMPM.simps(2))
qed

lemma q2:"prefix_lookup t l \<noteq> [] \<Longrightarrow>lookup_trie t (hd (FMPM t l))"
  apply(induction t l rule: FMPM.induct)
   apply simp
  by (metis (no_types, lifting) FMPM.simps(2) hd_Cons_tl list.case_eq_if list.sel(1) prefix_lookup_conv prefix_lookup_nil)


theorem match_correct:"\<forall>x\<in>set (FMPM t l). lookup_trie t x"
  proof(induction t l rule: FMPM.induct)
    case (1 b m)
    then show ?case by simp
  next
    case (2 b m x xs)
    show ?case 
    proof(cases "prefix_lookup (Trie_plus b m) (x#xs)" )
      case Nil
      then show ?thesis 
        using "2.IH"(1) by fastforce
    next
      case (Cons a list)
      then show ?thesis 
        by (metis "2.IH"(2) FMPM.simps(2) list.distinct(1) list.simps(5) prefix_lookup_lookup_trie set_ConsD)
    qed
  qed



end