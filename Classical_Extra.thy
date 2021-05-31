section \<open>Derived facts about classical registers\<close>

theory Classical_Extra
  imports Laws_Classical
begin

no_notation m_inv ("inv\<index> _" [81] 80)

lemma register_apply:
  assumes \<open>register F\<close>
  shows \<open>Some o register_apply F a = F (Some o a)\<close>
  sorry

lemma register_total:
  assumes \<open>register F\<close>
  assumes \<open>dom a = UNIV\<close>
  shows \<open>dom (F a) = UNIV\<close>
  sorry

lemma compatible_setter:
  assumes \<open>register F\<close> and \<open>register G\<close>
  defines \<open>sF \<equiv> snd (getter_setter F)\<close> and \<open>sG \<equiv> snd (getter_setter G)\<close> 
  shows \<open>compatible F G \<longleftrightarrow> (\<forall>a b. sF a o sG b = sG b o sF a)\<close>
  sorry

lemma register_from_getter_setter_compatibleI[intro]:
  assumes \<open>valid_getter_setter g s\<close>
  assumes \<open>valid_getter_setter g' s'\<close>
  assumes \<open>\<And>x y m. s x (s' y m) = s' y (s x m)\<close>
  shows \<open>compatible (register_from_getter_setter g s) (register_from_getter_setter g' s')\<close>
  sorry

lemma separating_update1:
  \<open>separating TYPE(_) {update1 x y | x y. True}\<close>
  by (smt (verit) mem_Collect_eq separating_def update1_extensionality)

definition "permutation_register (p::'b\<Rightarrow>'a) (a :: 'a update) = map_option (inv p) o a o p"

lemma permutation_register_preregister[simp]: "preregister (permutation_register p)"
  unfolding preregister_def
  sorry

lemma permutation_register_register: 
  fixes p :: "'b \<Rightarrow> 'a"
  assumes "bij p"
  shows "register (permutation_register p)"
  sorry

definition empty_var :: \<open>'a::{CARD_1} update \<Rightarrow> 'b update\<close> where
  "empty_var = register_from_getter_setter (\<lambda>_. undefined) (\<lambda>_ m. m)"

lemma register_empty_var[simp]: \<open>register empty_var\<close>
  sorry

lemma empty_var_compatible[simp]: \<open>register X \<Longrightarrow> compatible empty_var X\<close>
  sorry

lemma empty_var_compatible'[simp]: \<open>register X \<Longrightarrow> compatible X empty_var\<close>
  using compatible_sym empty_var_compatible by blast

subsubsection \<open>Example\<close>

record memory = 
  x :: "int*int"
  y :: nat

definition "X = register_from_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)"
definition "Y = register_from_getter_setter y (\<lambda>a b. b\<lparr>y:=a\<rparr>)"

lemma validX[simp]: \<open>valid_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma registerX[simp]: \<open>register X\<close>
  using X_def register_def validX by blast

lemma validY[simp]: \<open>valid_getter_setter y (\<lambda>a b. b\<lparr>y:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma registerY[simp]: \<open>register Y\<close>
  using Y_def register_def validY by blast

lemma compatibleXY[simp]: \<open>compatible X Y\<close>
  unfolding X_def Y_def by auto

end
