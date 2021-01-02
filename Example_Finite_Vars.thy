theory Example_Finite_Vars
  imports LValues_Typed "HOL-Word.Word"
begin

typedef mem = \<open>{f. \<forall>(n::string) (i::nat). f(n,i) \<in> {..i}}\<close>
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>]) by auto
setup_lifting type_definition_mem

definition idx_set where "idx_set (_::'a itself) = {..<CARD('a)}"
definition some_f where "some_f = (SOME f. bij_betw f (idx_set TYPE('val)) (UNIV::'val::finite set))"
definition some_f' :: "'val::finite\<Rightarrow>nat" where "some_f' = inv_into (idx_set TYPE('val)) some_f"

lemma bij_some_f: "bij_betw some_f (idx_set TYPE('val)) (UNIV::'val::finite set)"
  unfolding some_f_def 
  apply (rule someI_ex[where P=\<open>\<lambda>f. bij_betw f (idx_set TYPE('val)) (UNIV::'val set)\<close>])
  unfolding idx_set_def
  by (simp add: finite_same_card_bij)

lemma bij_some_f': "bij_betw some_f' (UNIV::'val set) (idx_set TYPE('val::finite))"
  by (simp add: bij_betw_inv_into bij_some_f some_f'_def)

lemma some_f_some_f'[simp]: "some_f (some_f' x) = x"
  by (metis UNIV_I bij_betw_inv_into_right bij_some_f some_f'_def)

lemma some_f'_some_f[simp]: "x \<in> idx_set TYPE('val::finite) \<Longrightarrow> some_f' (some_f x :: 'val) = x"
  unfolding some_f'_def
  by (meson bij_betw_inv_into_left bij_some_f)

lemma some_f'_leq: "some_f' (a::'a::finite) < CARD('a)"
proof -
  have "some_f' a \<in> idx_set TYPE('a)"
    by (meson bij_betw_apply bij_some_f' iso_tuple_UNIV_I)
  then show ?thesis
    unfolding idx_set_def by auto
qed

lift_definition var_getter :: "string \<Rightarrow> mem \<Rightarrow> 'a::finite" is
  "\<lambda>name mem. some_f (mem (name, card (UNIV::'a set)-1))".

lift_definition var_setter :: "string \<Rightarrow> 'a::finite \<Rightarrow> mem \<Rightarrow> mem" is
  "\<lambda>name v mem. mem ((name, card (UNIV::'a set)-1) := some_f' v)"
  using some_f'_leq less_Suc_eq_le by fastforce

definition var :: "string \<Rightarrow> (mem,'a::finite) lvalue" where
  "var name = mk_lvalue (var_getter name) (var_setter name)"

lemma valid_var[simp]: "valid_lvalue (var name :: (_,'val::finite) lvalue)"
  unfolding var_def 
proof (rule mk_lvalue_valid)
  fix m and a b :: 'val
  show "var_getter name (var_setter name a m) = a"
    apply transfer by auto
  show "var_setter name (var_getter name m) m = m"
    apply transfer 
    apply (subst some_f'_some_f) 
    unfolding idx_set_def apply auto
    by (metis Suc_le_lessD Suc_le_mono Suc_pred zero_less_card_finite)

  show "var_setter name a (var_setter name b m) = var_setter name a m"
    apply transfer by auto
qed

lemma var_setter_swap: 
  assumes "name \<noteq> name'"
  shows "var_setter name a (var_setter name' b m) = var_setter name' b (var_setter name a m)"
  apply (transfer fixing: name name')
  apply auto
  using assms by auto

lemma compatible_var: 
  "n \<noteq> m \<Longrightarrow> compatible_lvalues (var n) (var m)"
  unfolding var_def
  apply (rule mk_lvalue_compat)
  using valid_var unfolding var_def
  apply auto
  apply (subst var_setter_swap)
  by auto

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
