theory LValues_Typed
  imports LValues
begin

typedef ('mem, 'val) lvalue = \<open>{xopt :: ('mem,'val) lvalue_raw option.
  case xopt of None \<Rightarrow> True | Some x \<Rightarrow> 
    valid_lvalue x \<and> lv_range x = UNIV \<and> lv_domain x = UNIV}\<close>
  by (rule exI[of _ None], simp)
setup_lifting type_definition_lvalue

lift_definition valid_lvalue :: "('mem,'val) lvalue \<Rightarrow> bool" is "\<lambda>x. x \<noteq> None".

lift_definition compatible_lvalues :: "('mem,'val1) lvalue \<Rightarrow> ('mem,'val2) lvalue \<Rightarrow> bool" is
  \<open>\<lambda>x y. case (x,y) of (Some x, Some y) \<Rightarrow> LValues.compatible_lvalues x y | _ \<Rightarrow> False\<close>.

lift_definition lvalue_pair :: "('mem,'val1) lvalue \<Rightarrow> ('mem,'val2) lvalue \<Rightarrow> ('mem,'val1\<times>'val2) lvalue" is
  \<open>\<lambda>x y. case (x,y) of (Some x, Some y) \<Rightarrow> 
    if LValues.compatible_lvalues x y then Some (LValues.lvalue_pair x y) else None
    | _ \<Rightarrow> None\<close>
  apply (rename_tac x y; case_tac x; case_tac y)
     apply auto
  apply (simp add: lvalue_pair_def)
  by (simp add: lvalue_pair_def)

lemma "compatible_lvalues x y \<Longrightarrow> valid_lvalue (lvalue_pair x y)"
  apply transfer 
      apply (rename_tac x y; case_tac x; case_tac y)
  by auto

lemma "compatible_lvalues x y \<Longrightarrow> valid_lvalue x"
  apply transfer apply (rename_tac x y; case_tac x) by auto

lemma "compatible_lvalues x y \<Longrightarrow> valid_lvalue y"
  apply transfer apply (rename_tac x y; case_tac x; case_tac y) by auto

lift_definition lvalue_chain :: "('mem,'val1) lvalue \<Rightarrow> ('val1,'val2) lvalue \<Rightarrow> ('mem,'val2) lvalue" is
  \<open>\<lambda>x y. case (x,y) of (Some x, Some y) \<Rightarrow> Some (LValues.lvalue_chain x y)
    | _ \<Rightarrow> None\<close>
  apply (rename_tac x y; case_tac x; case_tac y) by auto

lemma "valid_lvalue x \<Longrightarrow> valid_lvalue y \<Longrightarrow> valid_lvalue (lvalue_chain x y)"
  apply transfer by auto

lift_definition the_invalid_lvalue :: "('mem,'val) lvalue" is "None"
  by auto

typedef 'mem memory_rest = "UNIV :: 'mem set set"..
setup_lifting type_definition_memory_rest

lift_definition split_memory :: "('mem,'val) lvalue \<Rightarrow> 'mem \<Rightarrow> ('val\<times>'mem memory_rest)" is
  "\<lambda>x m. case x of None \<Rightarrow> (undefined, {m})
                 | Some x \<Rightarrow> LValues.split_memory x m".

lift_definition setter :: "('mem,'val) lvalue \<Rightarrow> 'val \<Rightarrow> 'mem \<Rightarrow> 'mem" is
  "\<lambda>x. case x of Some x \<Rightarrow> lv_setter x | None \<Rightarrow> \<lambda>_. id".

lift_definition getter :: "('mem,'val) lvalue \<Rightarrow> 'mem \<Rightarrow> 'val" is
  "\<lambda>x. case x of Some x \<Rightarrow> lv_getter x | None \<Rightarrow> \<lambda>_. undefined".

lemma getter_pair[simp]:
  fixes x y
  assumes "compatible_lvalues x y"
  shows "getter (lvalue_pair x y) m = (getter x m, getter y m)"
  using assms apply (transfer fixing: m)
  apply (rename_tac x y; case_tac x; case_tac y)
     apply auto
  by (simp add: LValues.lvalue_pair_def)

lemma getter_setter[simp]:
  fixes x
  assumes "valid_lvalue x"
  shows "getter x (setter x a m) = a"
  using assms apply (transfer fixing: m)
  by auto

lemma getter_setter_compat[simp]:
  fixes x y
  assumes "compatible_lvalues x y"
  shows "getter x (setter y a m) = getter x m"
  using assms apply transfer
  apply (rename_tac x y a m; case_tac x; case_tac y)
  by auto


end
