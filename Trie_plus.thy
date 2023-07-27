theory Trie_plus
  imports Main "HOL-Library.AList"
begin


(*** trie_struction***)
datatype 'a trie = Trie_plus (is_end:bool) "('a * 'a trie)list"

thm trie.induct
lemma trie_induct [case_names Trie_plus, induct type]:
  "(\<And>b kvs. (\<And>k t. (k, t) \<in> set kvs \<Longrightarrow> P t) \<Longrightarrow> P (Trie_plus b kvs)) \<Longrightarrow> P t"
  by induction_schema (pat_completeness, lexicographic_order)

typ "nat trie"

(** empty **)
definition empty_trie :: "'a trie" where "empty_trie = Trie_plus False []"

value "Trie_plus False ([]::(nat * nat trie) list)"

fun is_empty_trie :: "'a trie \<Rightarrow> bool" where
  "is_empty_trie (Trie_plus v m) = (v = False \<and> m = [])"

(***  op ****)

(***  lookup_op ****)
fun lookup_trie :: "'a trie \<Rightarrow> 'a list \<Rightarrow> bool" where
"lookup_trie (Trie_plus b m) [] = b" |
"lookup_trie (Trie_plus b m) (k#ks) =
   (case map_of m k of
      None \<Rightarrow> False |
      Some st \<Rightarrow> lookup_trie st ks)"


(***  insert_op ****)
fun insert_trie :: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
  "insert_trie []      (Trie_plus b m)  = Trie_plus True m" |
  "insert_trie (k#ks)  (Trie_plus b m)  =
          Trie_plus b (AList.update_with_aux empty_trie k (insert_trie ks ) m)"




(***  delete_op ****)
fun delete_trie :: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie"
where
"delete_trie [] (Trie_plus b ts) = Trie_plus False ts" |
"delete_trie (k#ks) (Trie_plus b ts) =
   (case map_of ts k of
      None \<Rightarrow> Trie_plus b ts |
      Some t \<Rightarrow> let t' = delete_trie ks t 
                in if is_empty_trie t'
                   then Trie_plus b (AList.delete_aux k ts)
                   else Trie_plus b (AList.update k t' ts))"


(*** invar ***)

fun invar_trie :: "'a trie \<Rightarrow> bool" where
"invar_trie (Trie_plus b m) =
  (distinct (map fst m) \<and>
   (\<forall>(k, t) \<in> set m. \<not> is_empty_trie t \<and> invar_trie t))"



(****proof*****)

theorem invar_empty : "invar_trie empty_trie" 
   by(simp add:empty_trie_def)

lemma is_empty_conv: "is_empty_trie ts \<longleftrightarrow> ts = Trie_plus False []"
   by(cases ts)(simp)

lemma lookup_empty: "lookup_trie empty_trie = (\<lambda>_. False)"
proof
  fix ks show "lookup_trie empty_trie ks = (\<lambda>_. False) ks"
    by(cases ks)(auto simp: empty_trie_def)
qed

lemma lookup_empty': "lookup_trie (Trie_plus False []) ks = False"
by(simp add: lookup_empty[unfolded empty_trie_def])

lemma insert_trie_induct:
  "\<lbrakk>\<And>b ps. P [] (Trie_plus b ps); \<And>k ks b ps. (\<And>x. P ks x) \<Longrightarrow> P (k#ks) (Trie_plus b ps)\<rbrakk> \<Longrightarrow> P xs t"
by induction_schema (pat_completeness, lexicographic_order)

lemma insert_trie_Nil: "insert_trie []  (Trie_plus b ts) = Trie_plus True ts"
by(simp)

lemma insert_trie_Cons: "insert_trie (k#ks)  (Trie_plus b ts) =
  Trie_plus b (AList.update_with_aux (Trie_plus False []) k (insert_trie ks ) ts)" 
  by (simp add: empty_trie_def)


lemma lookup_insert:
  "lookup_trie (insert_trie ks  t) ks' = (if ks = ks' then True else lookup_trie t ks')"
proof(induct ks t arbitrary: ks' rule: insert_trie_induct)
  case (1 b ps)
  show ?case by(cases ks')(auto)
next
  case (2 k ks b ps)  
  show ?case apply(cases ks')
    apply(auto simp add: map_of_update_with_aux 2  split: option.split) 
    by (simp add: lookup_empty)
qed

lemma lookup_insert':
  "lookup_trie (insert_trie ks t) = (lookup_trie t)(ks := True)"
  apply(rule ext)
  by (simp add: lookup_insert)

theorem lookup_eq_True_iff:
assumes invar: "invar_trie ((Trie_plus b kvs) :: 'a trie)"
shows "lookup_trie (Trie_plus b kvs) ks = True \<longleftrightarrow>
    (ks = [] \<and> b = True) \<or>
    (\<exists>k t ks'. ks = k # ks' \<and> 
        (k, t) \<in> set kvs \<and> lookup_trie t ks' = True)"
proof (cases ks)
  case Nil thus ?thesis by simp
next
  case (Cons k ks')
  note ks_eq[simp] = Cons
  show ?thesis
  proof (cases "map_of kvs k")
    case None thus ?thesis 
      apply (simp)
      apply (auto simp add: map_of_eq_None_iff image_iff Ball_def)
    done
  next
    case (Some t') note map_eq = this
    from invar have dist_kvs: "distinct (map fst kvs)" by simp

    from map_of_eq_Some_iff[OF dist_kvs, of k] map_eq
    show ?thesis by simp metis
  qed
qed

theorem lookup_eq_False_iff:
assumes invar: "invar_trie ((Trie_plus b kvs) :: 'a trie)"
shows "lookup_trie (Trie_plus b kvs) ks = False \<longleftrightarrow>
    (ks = [] \<and> b = False) \<or>
    (\<exists>k ks'. ks = k # ks' \<and> (\<forall>t. (k, t) \<in> set kvs \<longrightarrow> lookup_trie t ks' = False))"
using lookup_eq_True_iff[of b kvs ks, OF invar]
  apply (cases ks)
  apply (auto)
done

lemma insert_not_empty: "\<not> is_empty_trie (insert_trie ks t)"
apply(cases t)
apply(rename_tac kvs)
apply(cases ks)
apply(case_tac [2] kvs)
apply (auto)
done

theorem invar_trie_insert: "invar_trie t \<Longrightarrow> invar_trie (insert_trie ks t)"
  apply(induct ks t rule: insert_trie_induct)
  apply(auto simp add: set_update_with_aux insert_not_empty  split: option.splits)
  by (simp add: invar_empty)
 
lemma is_empty_lookup_empty:
  "invar_trie t \<Longrightarrow> is_empty_trie t \<longleftrightarrow> lookup_trie t =( \<lambda>_. False)"
proof(induct t)
  case (Trie_plus vo kvs)
  thus ?case
    apply(cases kvs)
    apply(auto simp add: fun_eq_iff elim: allE[where x="[]"])
    apply (simp add: lookup_empty')
    apply(erule meta_allE)+
    apply(erule meta_impE)
    apply(rule disjI1)
    apply(fastforce intro: exI[where x="a # b" for a b])+
    done
qed

lemma delete_eq_empty_lookup_other_fail:
  "\<lbrakk> delete_trie ks t = Trie_plus False []; ks' \<noteq> ks \<rbrakk> \<Longrightarrow> lookup_trie t ks' = False"
proof(induct ks t arbitrary: ks' rule: delete_trie.induct)
  case 1 thus ?case by(auto simp add: neq_Nil_conv)
next
  case (2 k ks vo ts)
  show ?case
  proof(cases "map_of ts k")
    case (Some t)
    show ?thesis
    proof(cases ks')
      case (Cons k' ks'')
      show ?thesis
      proof(cases "k' = k")
        case False
        from Some Cons "2.prems"(1) have "AList.delete_aux k ts = []"
          by(clarsimp simp add: Let_def split: if_split_asm)
        with False have "map_of ts k' = None"
          by(cases "map_of ts k'")(auto dest: map_of_SomeD simp add: delete_aux_eq_Nil_conv)
        thus ?thesis using False Some Cons "2.prems"(1) by simp
      next
        case True
        with Some "2.prems" Cons show ?thesis
          by(clarsimp simp add: "2.hyps" Let_def is_empty_conv split: if_split_asm)
      qed
    qed(insert Some "2.prems"(1), simp add: Let_def split: if_split_asm)
  next
    case None thus ?thesis using "2.prems"(1)
      using lookup_trie.elims(2) by fastforce  
  qed
qed

lemma lookup_delete: "invar_trie t \<Longrightarrow>
  lookup_trie (delete_trie ks t) ks' =
  (if ks = ks' then False else lookup_trie t ks')"
proof(induct ks t arbitrary: ks' rule: delete_trie.induct)
  case 1 show ?case  by(cases ks')(auto)
next
  case (2 k ks vo ts)
  show ?case
  proof(cases ks')
    case Nil thus ?thesis by(simp split: option.split add: Let_def)
  next
    case [simp]: (Cons k' ks'')
    show ?thesis
    proof(cases "k' = k")
      case False thus ?thesis using "2.prems"
        by(auto simp add: Let_def update_conv' map_of_delete_aux split: option.split)
    next
      case [simp]: True
      show ?thesis
      proof(cases "map_of ts k")
        case None thus ?thesis by simp
      next
        case (Some t)
        thus ?thesis 
        proof(cases "is_empty_trie (delete_trie ks t)")
          case True
          with Some "2.prems" show ?thesis
            by(auto simp add: map_of_delete_aux is_empty_conv dest: delete_eq_empty_lookup_other_fail)
        next
          case False
          thus ?thesis using Some 2 by(auto simp add: update_conv')
        qed
      qed
    qed
  qed
qed

lemma lookup_delete':
  "invar_trie t \<Longrightarrow> lookup_trie (delete_trie ks t) = (lookup_trie t)(ks := False)"
by(rule ext)(simp add: lookup_delete)

theorem invar_trie_delete:
  "invar_trie t \<Longrightarrow> invar_trie (delete_trie ks t)"
proof(induct ks t rule: delete_trie.induct)
  case 1 thus ?case by simp
next
  case (2 k ks vo ts)
  show ?case
  proof(cases "map_of ts k")
    case None
    thus ?thesis using "2.prems" by simp
  next
    case (Some t)
    with "2.prems" have "invar_trie t" by auto
    with Some have "invar_trie (delete_trie ks t)" by(rule 2)
    from "2.prems" Some have distinct: "distinct (map fst ts)" "\<not> is_empty_trie t" by auto
    show ?thesis
    proof(cases "is_empty_trie (delete_trie ks t)")
      case True
      { fix k' t'
        assume k't': "(k', t') \<in> set (AList.delete_aux k ts)"
        with distinct have "map_of (AList.delete_aux k ts) k' = Some t'" by simp
        hence "map_of ts k' = Some t'" using distinct
          by (auto 
            simp del: map_of_eq_Some_iff
            simp add: map_of_delete_aux 
            split: if_split_asm)
        with "2.prems" have "\<not> is_empty_trie t' \<and> invar_trie t'" by auto }
      with "2.prems" have "invar_trie (Trie_plus vo (AList.delete_aux k ts))" by auto
      thus ?thesis using True Some by(simp)
    next
      case False
      { fix k' t'
        assume k't':"(k', t') \<in> set (AList.update k (delete_trie ks t) ts)"
        hence "map_of (AList.update k (delete_trie ks t) ts) k' = Some t'"
          using "2.prems" by(auto simp add: distinct_update)
        hence eq: "((map_of ts)(k \<mapsto> delete_trie ks t)) k' = Some t'" unfolding update_conv .
        have "\<not> is_empty_trie t' \<and> invar_trie t'"
        proof(cases "k' = k")
          case True
          with eq have "t' = delete_trie ks t" by simp
          with \<open>invar_trie (delete_trie ks t)\<close> False
          show ?thesis by simp
        next
          case False
          with eq distinct have "(k', t') \<in> set ts" by simp
          with "2.prems" show ?thesis by auto
        qed }
      thus ?thesis using Some "2.prems" False by(auto simp add: distinct_update)
    qed
  qed
qed


lemma lookup_trie_case: "lookup_trie (Trie_plus b m) xs =
  (case xs of
   [] \<Rightarrow> b |
   x # ys \<Rightarrow> (case (map_of m x) of None \<Rightarrow> False | Some t \<Rightarrow> lookup_trie t ys))"
  by(cases xs) auto

definition trie_set :: "'a trie \<Rightarrow> 'a list set" where
[simp]: "trie_set t = {xs. lookup_trie t xs}"


lemma isin_set: "lookup_trie t xs = (xs \<in> trie_set t)"
by simp

theorem empty_trie_set:"is_empty_trie t \<Longrightarrow> trie_set t = {}"
  apply(cases "t") 
  using lookup_empty' by auto


theorem "lookup_trie t ls \<Longrightarrow> ls \<in> (trie_set t)"
  by(cases ls)auto

theorem "\<not>(lookup_trie t ls) \<Longrightarrow> ls \<notin> (trie_set t)"
  by(cases ls)auto

theorem set_insert: "trie_set (insert_trie xs t) = trie_set t \<union> {xs}"
  apply (induction xs t rule: insert_trie.induct)  
   apply (auto simp: lookup_trie_case)  
      apply (simp add: list.case_eq_if)+ 
  apply (metis insert_trie.simps(2) list.exhaust_sel lookup_insert lookup_trie.simps(2)) 
  apply (metis insert_trie.simps(2) lookup_insert lookup_trie.simps(2)) 
  by (metis insert_trie.simps(2) lookup_insert lookup_trie_case)


theorem set_delete: "invar_trie t \<Longrightarrow>trie_set (delete_trie xs t) = trie_set t - {xs}" 
  apply (induction xs t rule: delete_trie.induct) 
  apply (smt (z3) Diff_idemp Diff_insert_absorb set_insert Un_insert_right delete_trie.simps(1) insert_trie.simps(1) isin_set lookup_trie.simps(1) sup_bot_right)
  apply (auto simp: lookup_trie_case) 
  apply (metis delete_trie.simps(2) invar_trie.simps lookup_delete lookup_trie_case)  
  apply (metis delete_trie.simps(2) invar_trie.simps lookup_delete) 
  by (metis delete_trie.simps(2) invar_trie.simps lookup_delete lookup_trie_case)


end





