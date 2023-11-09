theory match
  imports Main Trie_plus
begin

(***chinese/english ***)
datatype ch = English nat | Chinese nat nat

(**** FMPM  ****)
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



(*** substring ***)
definition is_substring :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_substring s1 s2 = (\<exists>s3 s4. s2 = s3 @ s1 @ s4)"

fun startsWith :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "startsWith [] ys = True" |
        "startsWith (x # xs) [] = False" |
        "startsWith (x # xs) (y # ys) = (if x = y then startsWith xs ys else False)"


fun is_Substring :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_Substring x [] = (x = [])" |
  "is_Substring x (y # ys) = (startsWith x (y # ys) \<or> is_Substring x ys)"
value "is_Substring  ''bc'' ''abcde''"


(***is_Substring proof ****)
lemma is_sub_is_sub:"startsWith xs ys = (\<exists>ls. xs@ls = ys)" 
  by(induct xs ys rule: startsWith.induct) auto

lemma startsWith_sub:"startsWith x ys \<Longrightarrow> is_substring x ys"
  by(auto simp:is_sub_is_sub is_substring_def) 

lemma is_substring_add:"is_substring x ys \<Longrightarrow> is_substring x (y#ys)" 
  apply(simp add: is_substring_def) 
  apply(erule exE)+
  apply (rule_tac x="y # s3" in exI)
  apply (rule_tac x="s4" in exI)
  apply simp
  done

theorem is_Substring_equiv_is_substring:
  "is_Substring x y = is_substring x y"
proof(induct x y rule: is_Substring.induct)
  case (1 x)
  then show ?case 
    by (simp add: is_substring_def)
next
  case (2 x y ys)
  then show ?case 
  proof(cases)
    assume 01:"startsWith x (y#ys)" thus ?case using 2 is_Substring.simps(2)[of x y ys]
      by (metis  startsWith_sub)
  next
    assume 02:"\<not> startsWith x (y#ys)" thus ?case using 2 is_substring_add is_Substring.simps(2) 
      by (smt (verit, best) append_self_conv2 is_sub_is_sub is_substring_def list.sel(3) tl_append2)
  qed
qed




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


lemma startsWith_add:"startsWith xs ys \<Longrightarrow> startsWith (a#xs) (a#ys)"
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

lemma lookup_trie_look_up:"lookup_trie t l \<Longrightarrow> look_up t l = l"
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
        by (simp add: lookup_trie_look_up)        
  qed
qed

lemma prefix_lookup_startsWith:"prefix_lookup t l = str \<Longrightarrow> startsWith str l "
proof(induct t )
  case (Trie_plus b kvs)
  then show ?case 
    by (metis look_up_pre prefix_lookup_nil prefix_lookup_conv startsWith.simps(1))
qed


lemma FMPM_empty':"FMPM t [] = []"
  apply(induct t)
  by auto
lemma FMPM_empty:"FMPM empty_trie l = []"
  apply(induct l)
  using FMPM_empty' apply blast
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

lemma match_is_sub:"\<forall>x\<in>set (FMPM t l).  is_Substring  x l"
proof(induction t l rule: FMPM.induct)
  case (1 b m)
  then show ?case 
    by auto
next
  case (2 b m x xs)
  then show ?case 
    proof(cases "prefix_lookup (Trie_plus b m) (x#xs)" )
      case Nil
      then show ?thesis 
        by (simp add: "2.IH"(1))
    next
      case (Cons a list)
      then show ?thesis  apply auto 
        apply (metis Cons prefix_lookup_startsWith startsWith.simps(3))
        using "2.IH"(2)Cons apply blast
         apply (metis prefix_lookup_startsWith Cons startsWith.simps(3))
        using "2.IH"(2) Cons by blast
    qed
qed


lemma prefix_lookup_hd:"prefix_lookup t l \<noteq> [] \<Longrightarrow>lookup_trie t (hd (FMPM t l))"
  apply(induction t l rule: FMPM.induct)
   apply simp
  by (metis (no_types, lifting) FMPM.simps(2) hd_Cons_tl list.case_eq_if list.sel(1) prefix_lookup_conv prefix_lookup_nil)


lemma match_lookup_trie:"\<forall>x\<in>set (FMPM t l). lookup_trie t x"
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
        by (metis "2.IH"(2) FMPM.simps(2) list.distinct(1) list.simps(5) 
              prefix_lookup_lookup_trie set_ConsD)
    qed
  qed

theorem match_correct:"\<forall>x\<in>set (FMPM t l). (lookup_trie t x)\<and>is_Substring x l"
  using match_lookup_trie match_is_sub by blast

export_code empty_trie insert_trie lookup_trie delete_trie FMPM in Haskell

end