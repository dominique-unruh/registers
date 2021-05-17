section \<open>Derived facts about classical registers\<close>

theory Classical_Extra
  imports Laws_Classical
begin

no_notation m_inv ("inv\<index> _" [81] 80)

lemma register_single_valued:
  assumes registerF: \<open>register F\<close>
  assumes single: \<open>single_valued a\<close>
  shows \<open>single_valued (F a)\<close>
proof -
  have "mono F"
    by (simp add: registerF preregister_mono)
  
  from single
  have contains_Id: "a\<inverse> O a \<subseteq> Id"
    by (auto simp add: single_valued_def)

  have "(F a)\<inverse> O F a = F (a\<inverse> O a)"
    by (metis registerF register_def)
  also have \<open>\<dots> \<subseteq> F Id\<close>
    using \<open>mono F\<close> contains_Id
    by (meson monoD)
  also have \<open>\<dots> = Id\<close>
    using registerF register_def by blast
  
  finally show "single_valued (F a)"
    by (auto simp: single_valued_def)
qed



lemma register_fulldom:
  assumes registerF: \<open>register F\<close>
  assumes adom: \<open>Domain a = UNIV\<close>
  shows \<open>Domain (F a) = UNIV\<close>
proof -
  have "mono F"
    by (simp add: registerF preregister_mono)
  
  from adom
  have contains_Id: "a O a\<inverse> \<supseteq> Id"
    by (auto simp add: converse_def relcomp_def relcompp_apply)
  
  have "F a O (F a)\<inverse> = F (a O a\<inverse>)"
    by (metis registerF register_def)
  also have \<open>\<dots> \<supseteq> F Id\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    using \<open>mono F\<close> contains_Id
    by (meson monoD)
  also have \<open>\<dots> = Id\<close>
    using registerF register_def by blast
  
  finally show "Domain (F a) = UNIV"
    by auto
qed


lemma register_fullrange:
  assumes registerF: \<open>register F\<close>
  assumes arange: \<open>Range a = UNIV\<close>
  shows \<open>Range (F a) = UNIV\<close>
  using register_fulldom[OF registerF arange[folded Domain_converse]]
  by (metis Domain_converse registerF register_def)


definition "permutation_register (p::'b\<Rightarrow>'a) a = {(inv p x, inv p y)| x y. (x,y) \<in> a}"

lemma permutation_register_hom[simp]: "preregister (permutation_register p)"
  unfolding preregister_def
  apply (rule exI[of _ \<open>{((x,y), (inv p x, inv p y))| x y. True}\<close>])
  by (auto simp: permutation_register_def[abs_def])

lemma permutation_register_register: 
  fixes p :: "'b \<Rightarrow> 'a"
  assumes "bij p"
  shows "register (permutation_register p)"
proof (unfold register_def, intro conjI allI)
  show \<open>preregister (permutation_register p)\<close>
    by simp
  show \<open>permutation_register p Id = Id\<close>
    unfolding permutation_register_def Id_def apply auto
    by (simp add: assms bij_inv_eq_iff)
  fix a a'
  show \<open>permutation_register p a O permutation_register p a' = permutation_register p (a O a')\<close>
    apply (auto simp: permutation_register_def relcomp_def relcompp_apply)
    by (metis assms bij_def surj_f_inv_f)
  show \<open>permutation_register p (a\<inverse>) = (permutation_register p a)\<inverse>\<close>
    by (auto simp: permutation_register_def)
qed

definition register_from_setter :: \<open>('b\<Rightarrow>'a) \<Rightarrow> ('a\<Rightarrow>'b\<Rightarrow>'b) \<Rightarrow> ('a,'b) preregister\<close> where
  \<open>register_from_setter g s a = {(s ax b, s ay b) | b ax ay. (ax,ay) \<in> a}\<close>

lemma register_from_setter_hom[simp]: "preregister (register_from_setter g s)"
  unfolding preregister_def 
  apply (rule exI[of _ \<open>{((ax, ay), (s ax b, s ay b))| ax ay b. True}\<close>])
  apply (rule ext)
  by (auto simp: register_from_setter_def[abs_def] Image_def[abs_def])

definition "valid_getter_setter g s \<longleftrightarrow> 
  (\<forall>b. b = s (g b) b) \<and> (\<forall>a b. g (s a b) = a) \<and> (\<forall>a a' b. s a (s a' b) = s a b)"

(* A bit stronger than register_from_setter_register *)
lemma register_from_setter_register': 
  fixes s :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes \<open>\<And>b. \<exists>b'. b = s (g b) b'\<close>
  assumes \<open>\<And>a b. g (s a b) = a\<close>
  assumes \<open>\<And>a a' b1 b2. s a b1 = s a b2 \<Longrightarrow> s a' b1 = s a' b2\<close>
  shows "register (register_from_setter g s)"
proof (unfold register_def, intro conjI allI)
  show \<open>preregister (register_from_setter g s)\<close>
    by simp
  show \<open>register_from_setter g s Id = Id\<close>
    unfolding register_from_setter_def
    apply (auto simp: register_from_setter_def)
    using assms by blast

  fix a 
  show \<open>register_from_setter g s (a\<inverse>) = (register_from_setter g s a)\<inverse>\<close>
    unfolding register_from_setter_def
    by (auto simp: register_from_setter_def)

  fix a'
  show \<open>register_from_setter g s a O register_from_setter g s a' = register_from_setter g s (a O a')\<close>
    unfolding register_from_setter_def
    apply (auto simp: register_from_setter_def relcomp_def relcompp_apply)
    using assms
    by metis
qed


lemma register_from_setter_register[simp]:
  fixes s :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes "valid_getter_setter g s"
  shows "register (register_from_setter g s)"
  apply (rule register_from_setter_register'[where g=g])
  using assms unfolding valid_getter_setter_def by metis+

lemma register_from_setter_set:
  assumes "valid_getter_setter g s"
  shows \<open>register_from_setter g s {(a, a0)|a. True} = {(b, s a0 b)|b. True}\<close>
  using assms by (auto simp: valid_getter_setter_def register_from_setter_def)

lemma register_from_setter_map:
  assumes "valid_getter_setter g s"
  shows \<open>register_from_setter g s {(a, f a)|a. True} = {(b, s (f (g b)) b)|b. True}\<close>
  using assms by (auto simp: valid_getter_setter_def register_from_setter_def)


lemma register_from_setter_compat:
  assumes [simp]: "valid_getter_setter g1 s1"
  assumes [simp]: "valid_getter_setter g2 s2"
  assumes \<open>\<And>a1 a2 b. s1 a1 (s2 a2 b) = s2 a2 (s1 a1 b)\<close>
  shows \<open>compatible (register_from_setter g1 s1) (register_from_setter g2 s2)\<close>
  unfolding compatible_def apply simp
  using assms unfolding valid_getter_setter_def
  apply (auto simp add: register_from_setter_def relcomp_def relcompp_apply)
  by metis+

definition setter_from_register :: \<open>('a,'b) preregister \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)\<close> where
  \<open>setter_from_register F a' m = (THE m'. (m,m') \<in> F {(a, a') |a. True})\<close>

definition getter_from_register :: \<open>('a,'b) preregister \<Rightarrow> ('b \<Rightarrow> 'a)\<close> where
  \<open>getter_from_register F m = (THE a. (m,m) \<in> F {(a,a)})\<close>

lemma setter_from_register:
  assumes \<open>valid_getter_setter g s\<close>
  shows \<open>setter_from_register (register_from_setter g s) = s\<close>
  unfolding setter_from_register_def
  apply (subst register_from_setter_set[OF assms])
  by auto

lemma getter_from_register:
  assumes \<open>valid_getter_setter g s\<close>
  shows \<open>getter_from_register (register_from_setter g s) = g\<close>
proof -
  from assms
  have \<open>\<exists>!a. \<exists>b. m = s a b\<close> for m
    unfolding valid_getter_setter_def 
    apply auto by metis
  with assms show ?thesis
    unfolding getter_from_register_def register_from_setter_def valid_getter_setter_def 
    apply (auto intro!:ext)
    by (smt (verit, ccfv_threshold) Uniq_def the1_equality')
qed

definition empty_var :: \<open>'a::{CARD_1} rel \<Rightarrow> 'b::finite rel\<close> where
  "empty_var a = (if a={} then {} else Id)"

lemma register_empty_var[simp]: \<open>register empty_var\<close>
proof (unfold register_def, intro conjI allI)
  show \<open>preregister empty_var\<close>
    unfolding empty_var_def preregister_def
    by (rule exI[of _ \<open>UNIV \<times> Id\<close>], rule ext, auto)
  show \<open>empty_var Id = Id\<close>
    unfolding empty_var_def by auto
  fix a b :: "'a update"
  show \<open>empty_var a O empty_var b = empty_var (a O b)\<close>
    unfolding empty_var_def apply auto
    by (metis CARD_1_UNIV Image_singleton_iff empty_iff relcomp.relcompI)
  show \<open>empty_var (a\<inverse>) = (empty_var a)\<inverse>\<close>
    unfolding empty_var_def by auto
qed

lemma empty_var_compatible[simp]: \<open>register X \<Longrightarrow> compatible empty_var X\<close>
  apply (rule compatibleI)
  using [[simproc del: compatibility_warn]]
  by (auto simp: empty_var_def)

lemma empty_var_compatible'[simp]: \<open>register X \<Longrightarrow> compatible X empty_var\<close>
  using compatible_sym empty_var_compatible by blast


(* TODO: define setter_from_register and to get the setter back. This 
         then implies that registers and getter/setters are the same. *)

subsubsection \<open>Example\<close>

record memory = 
  x :: "int*int"
  y :: nat

definition "X = register_from_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)"

lemma valid: \<open>valid_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma register: \<open>register X\<close>
  by (simp add: valid X_def)


end
