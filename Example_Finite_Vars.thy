theory Example_Finite_Vars
  imports LValues_Typed "HOL-Word.Word"
begin

typedef mem = \<open>{f. \<forall>(n::string) (i::nat). f(n,i) \<in> {..i}}\<close>
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>]) by auto

definition var_raw0 :: "string \<Rightarrow> nat \<Rightarrow> (mem,nat) lvalue_raw" where
  "var_raw0 n i = \<lparr> lv_domain = UNIV, lv_range = {..<i},
    lv_getter = \<lambda>m. Rep_mem m (n,i-1),
    lv_setter = \<lambda>a m. Abs_mem (fun_upd (Rep_mem m) (n,i-1) a) \<rparr>"

lemma valid_var_raw0:
  assumes "i \<noteq> 0"
  shows "LValues.valid_lvalue (var_raw0 n i)"
  unfolding var_raw0_def apply (rule valid_lvalueI)
  using Rep_mem Rep_mem_inverse apply auto
     apply (subst Abs_mem_inverse)
      apply auto
   apply (subst Abs_mem_inverse)
    apply auto
  by (metis Suc_le_lessD Suc_le_mono Suc_pred assms neq0_conv)

lemma var_raw0_domain[simp]: "lv_domain (var_raw0 n i) = UNIV"
  by (simp add: var_raw0_def)

lemma var_raw0_range[simp]: "lv_range (var_raw0 n i) = {..<i}"
  by (simp add: var_raw0_def)

definition some_f where "some_f = (SOME f. bij_betw f {..<card (UNIV::'val::finite set)} (UNIV::'val set))"

lemma bij_some_f: "bij_betw some_f {..<card (UNIV::'val::finite set)} (UNIV::'val set)"
  unfolding some_f_def
  apply (rule someI_ex[where P=\<open>\<lambda>f. bij_betw f {..<card (UNIV::'val set)} (UNIV::'val set)\<close>])
  by (simp add: finite_same_card_bij)

lemma inj_some_f: "inj_on (some_f::_\<Rightarrow>'val::finite) {..<card (UNIV::'val set)}"
  using bij_betw_imp_inj_on bij_some_f by blast

definition var_raw :: "string \<Rightarrow> (mem,'val::finite) lvalue_raw" where
  "var_raw n = lvalue_map some_f
     (var_raw0 n (card (UNIV::'val set)))"

lemma valid_var_raw[simp]:
  shows "LValues.valid_lvalue (var_raw n)"
  unfolding var_raw_def
  apply (rule valid_lvalue_map)
   apply (rule valid_var_raw0, simp)
  unfolding var_raw0_def
  using inj_some_f by simp

lemma range_var_raw[simp]:
  "lv_range (var_raw n) = UNIV"
  unfolding var_raw_def apply simp
  using bij_some_f
  using bij_betw_imp_surj_on by blast

lemma domain_var_raw[simp]:
  "lv_domain (var_raw n) = UNIV"
  unfolding var_raw_def by simp

lift_definition var :: "string \<Rightarrow> (mem,'val::finite) lvalue" is "Some o var_raw"
  by auto

lemma valid_var[simp]: "valid_lvalue (var n)"
  apply transfer by auto

lemma compatible_var_raw0:
  assumes "n \<noteq> m" and "i \<noteq> 0" and "j \<noteq> 0"
  shows "LValues.compatible_lvalues (var_raw0 n i) (var_raw0 m j)"
  apply (rule compatible_lvalues.intros)
     apply (auto simp: assms valid_var_raw0)
  unfolding var_raw0_def apply (simp add: Rep_mem_inverse)
  using Rep_mem apply (subst Abs_mem_inverse; auto)
  using Rep_mem apply (subst Abs_mem_inverse; auto)
  by (simp add: assms(1) fun_upd_twist)

lemma compatible_var: 
  "n \<noteq> m \<Longrightarrow> compatible_lvalues (var n) (var m)"
  apply transfer apply simp
  unfolding var_raw_def
  apply (rule lvalue_map_compat1)
  apply (rule lvalue_map_compat2)
  apply auto
    apply (rule compatible_var_raw0)
  using inj_some_f by auto

definition x::"(mem,bool)lvalue" where "x = var ''x''"
definition y::"(mem,32 word)lvalue" where "y = var ''y''"

lemma valid_x[simp]: "valid_lvalue x"
  by (simp add: x_def)

lemma valid_y[simp]: "valid_lvalue y"
  by (simp add: y_def)

lemma compat_xy[simp]: "compatible_lvalues x y"
  by (simp add: compatible_var x_def y_def)

lemma compat_yx[simp]: "compatible_lvalues y x"
  by (simp add: compatible_var x_def y_def)



lemma test:
  "getter (lvalue_pair x y) (setter x True (setter y 99 m))
      = (True, 99)"

  by simp

end
