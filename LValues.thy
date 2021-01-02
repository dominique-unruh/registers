theory LValues
  imports Main
begin

record ('mem,'val) lvalue = 
  lv_domain :: \<open>'mem set\<close>
  lv_range :: \<open>'val set\<close>
  lv_getter :: \<open>'mem \<Rightarrow> 'val\<close>
  lv_setter :: \<open>'val \<Rightarrow> 'mem \<Rightarrow> 'mem\<close>

inductive valid_lvalue where
  "\<lbrakk>\<And>a m. m \<in> D \<Longrightarrow> a \<in> R \<Longrightarrow> g (s a m) = a;
    \<And>m. m \<in> D \<Longrightarrow> s (g m) m = m;
    \<And>a b m. m \<in> D \<Longrightarrow> a \<in> R \<Longrightarrow> b \<in> R \<Longrightarrow> s a (s b m) = s a m;
    \<And>m. m \<in> D \<Longrightarrow> g m \<in> R;
    \<And>a m. m \<in> D \<Longrightarrow> a \<in> R \<Longrightarrow> s a m \<in> D\<rbrakk>
   \<Longrightarrow> valid_lvalue \<lparr> lv_domain=D, lv_range=R, lv_getter=g, lv_setter=s \<rparr>"

lemmas valid_lvalueI = valid_lvalue.intros
    [case_names get_set set_get set_set get_range set_domain (* domain_inhabited *)]

inductive compatible_lvalues where
  "\<lbrakk>valid_lvalue x; valid_lvalue y;
    lv_domain x = lv_domain y;
    \<And>a b m. m \<in> lv_domain x \<Longrightarrow> a \<in> lv_range x \<Longrightarrow> b \<in> lv_range y \<Longrightarrow>
            lv_setter x a (lv_setter y b m) = lv_setter y b (lv_setter x a m)\<rbrakk>
    \<Longrightarrow> compatible_lvalues x y"

definition lvalue_pair where
  "lvalue_pair x y = \<lparr> lv_domain = lv_domain x, lv_range = lv_range x \<times> lv_range y,
    lv_getter = \<lambda>m. if m \<in> lv_domain x then (lv_getter x m, lv_getter y m) else undefined,
    lv_setter = \<lambda>(a,b). lv_setter x a \<circ> lv_setter y b\<rparr>"

lemma set_domain[simp]:
  assumes "valid_lvalue x"
  assumes "m \<in> lv_domain x"
  assumes "a \<in> lv_range x"
  shows "lv_setter x a m \<in> lv_domain x"
  using assms apply cases 
  by auto

lemma get_set[simp]:
  assumes "valid_lvalue x"
  assumes "m \<in> lv_domain x"
  assumes "a \<in> lv_range x"
  shows "lv_getter x (lv_setter x a m) = a"
  using assms apply cases by auto

lemma set_get[simp]:
  assumes "valid_lvalue x"
  assumes "m \<in> lv_domain x"
  shows "lv_setter x (lv_getter x m) m = m"
  using assms apply cases by auto

lemma set_set[simp]:
  assumes "valid_lvalue x"
  assumes "m \<in> lv_domain x"
  assumes "a \<in> lv_range x"
  assumes "b \<in> lv_range x"
  shows "lv_setter x a (lv_setter x b m) = lv_setter x a m"
  using assms apply cases by auto

lemma get_range[simp]:
  assumes "valid_lvalue x"
  assumes "m \<in> lv_domain x"
  shows "lv_getter x m \<in> lv_range x"
  using assms apply cases by auto

(* lemma domain_inhabited[simp]:
  assumes "valid_lvalue x"
  shows "lv_domain x \<noteq> {}"
  using assms apply cases by auto

lemma range_inhabited[simp]:
  assumes "valid_lvalue x"
  shows "lv_range x \<noteq> {}"
  using assms apply cases by auto *)

lemma lvalue_pair_valid[simp]:
  fixes x :: "('mem,'val1) lvalue" and y :: "('mem,'val2) lvalue" 
  assumes "compatible_lvalues x y"
  shows "valid_lvalue (lvalue_pair x y)"
  using assms apply cases
  unfolding lvalue_pair_def apply (rule valid_lvalueI)
       apply auto
           apply (metis get_set set_domain)
  using set_domain apply fastforce
    apply (metis set_domain)
  using set_domain apply fastforce
  using set_domain by fastforce


definition lvalue_chain where
  "lvalue_chain x y = \<lparr> lv_domain = lv_domain x, lv_range = lv_range y,
                        lv_getter = lv_getter y \<circ> lv_getter x,
                        lv_setter = \<lambda>a m. lv_setter x (lv_setter y a (lv_getter x m)) m\<rparr>"

lemma lvalue_chain_domain[simp]: "lv_domain (lvalue_chain x y) = lv_domain x"
  by (simp add: lvalue_chain_def)

lemma lvalue_chain_range[simp]: "lv_range (lvalue_chain x y) = lv_range y"
  by (simp add: lvalue_chain_def)

lemma lvalue_chain_valid[simp]:
  assumes "valid_lvalue x"
  assumes "valid_lvalue y"
  assumes "lv_range x = lv_domain y"
  shows "valid_lvalue (lvalue_chain x y)"
  using assms apply cases
  unfolding lvalue_chain_def apply (rule valid_lvalueI)
  by auto


inductive_set same_except for x where
  "\<lbrakk>m \<in> lv_domain x; a \<in> lv_range x\<rbrakk> \<Longrightarrow> (m, lv_setter x a m) \<in> same_except x"

lemma equiv_same_except:
  assumes "valid_lvalue x"
  shows "equiv (lv_domain x) (same_except x)"
proof (rule equivI)
  show "refl_on (lv_domain x) (same_except x)"
    apply (rule refl_onI)
    using assms same_except.simps apply fastforce
    by (metis assms get_range same_except.simps set_get)
  show "sym (same_except x)"
    by (metis (no_types, lifting) assms get_range same_except.simps set_domain set_get set_set sym_def)
  show "trans (same_except x)"
    by (smt assms same_except.simps set_set trans_def)
qed

definition memory_except where 
  "memory_except x = lv_domain x // same_except x"

definition split_memory where
  "split_memory x m = (lv_getter x m, same_except x `` {m})"

definition join_memory where
  "join_memory x = (\<lambda>(a,m). the_elem (lv_setter x a ` m))"

lemma split_memory_range:
  assumes [simp]: "valid_lvalue x"
  assumes [simp]: "m \<in> lv_domain x"
  shows "split_memory x m \<in> lv_range x \<times> memory_except x"
  by (simp add: split_memory_def memory_except_def quotientI)

lemma congruent_lv_setter:
  assumes "valid_lvalue x" and "a \<in> lv_range x"
  shows "congruent (same_except x) (lv_setter x a)"
  apply (rule congruentI) 
  apply (cases rule: same_except.cases)
  using assms by auto

lemma apply_congruent:
  assumes "f respects r"
  assumes "equiv A r"
  assumes "x \<in> A"
  shows "f ` r `` {x} = {f x}"
  using assms
  using congruentD equiv_class_self image_insert by fastforce

lemma join_split_memory[simp]:
  assumes "valid_lvalue x"
  assumes "m \<in> lv_domain x"
  shows "join_memory x (split_memory x m) = m"
proof -
  define a m' where "a = lv_getter x m" and "m' = same_except x `` {m}"
  have sm: "split_memory x m = (a,m')"
    by (simp add: a_def m'_def split_memory_def)
  have "congruent (same_except x) (lv_setter x a)" 
    and "equiv (lv_domain x) (same_except x)"
    and "m \<in> lv_domain x"
    by (auto simp add: a_def assms(1) assms(2) congruent_lv_setter equiv_same_except)
  then have s: "lv_setter x a ` m' = {lv_setter x a m}"
    unfolding m'_def
    by (meson apply_congruent) 
  then show ?thesis
    unfolding sm join_memory_def a_def using assms by auto
qed

lemma split_join_memory[simp]:
  assumes [simp]: "valid_lvalue x"
  assumes "am \<in> lv_range x \<times> memory_except x"
  shows "split_memory x (join_memory x am) = am"
proof -
  obtain a m' where am_def: "am = (a,m')" by force
  then have a[simp]: "a \<in> lv_range x" and "m' \<in> lv_domain x // same_except x"
    using assms unfolding memory_except_def by auto
  then obtain m where m[simp]: "m \<in> lv_domain x" and m': "m' = same_except x `` {m}"
    using quotientE by blast
  have am': "am = split_memory x (lv_setter x a m)"
    unfolding split_memory_def am_def apply simp
    by (metis a assms(1) equiv_class_eq equiv_same_except m m' same_except.intros)
  show ?thesis
    unfolding am'
    apply (subst join_split_memory)
    by auto
qed

lemma join_memory_range:
  assumes [simp]: "valid_lvalue x"
  assumes [simp]: "am \<in> lv_range x \<times> memory_except x"
  shows "join_memory x am \<in> lv_domain x"
  by (smt ImageE Pair_inject SigmaE SigmaI assms(1) assms(2) equiv_Eps_in equiv_same_except memory_except_def same_except.simps singletonD split_join_memory split_memory_def)

lemma bij_split_memory:
  assumes [simp]: "valid_lvalue x"
  shows "bij_betw (split_memory x) (lv_domain x) (lv_range x \<times> memory_except x)"
  apply (rule bij_betw_byWitness[where f'="join_memory x"])
  apply auto
  apply (simp add: split_memory_def)
  apply (simp add: memory_except_def quotientI split_memory_def)
  apply (rule join_memory_range)
  by auto

lemma bij_join_memory:
  assumes [simp]: "valid_lvalue x"
  shows "bij_betw (join_memory x) (lv_range x \<times> memory_except x) (lv_domain x)"
  apply (rule bij_betw_byWitness[where f'="split_memory x"])
     apply auto
    apply (simp add: join_memory_range)
   apply (simp add: split_memory_def)
  by (simp add: memory_except_def quotientI split_memory_def)

lemma get_split_memory[simp]:
  assumes [simp]: "valid_lvalue x"
  assumes [simp]: "m \<in> lv_domain x"
  shows "fst (split_memory x m) = lv_getter x m"
  unfolding split_memory_def by simp

end

