theory LValues_Typed
  imports LValues
begin

typedef ('mem, 'val) lvalue = \<open>{xopt :: ('mem,'val) lvalue_raw option.
  case xopt of None \<Rightarrow> True | Some x \<Rightarrow> 
    valid_lvalue x \<and> lv_range x = UNIV \<and> lv_domain x = UNIV}\<close>
  by (rule exI[of _ None], simp)
setup_lifting type_definition_lvalue

lift_definition valid_lvalue :: "('mem,'val) lvalue \<Rightarrow> bool" is "\<lambda>x. x \<noteq> None".

(* lift_definition compatible_lvalues :: "('mem,'val1) lvalue \<Rightarrow> ('mem,'val2) lvalue \<Rightarrow> bool" is
  \<open>\<lambda>x y. case (x,y) of (Some x, Some y) \<Rightarrow> LValues.compatible_lvalues x y | _ \<Rightarrow> False\<close>. *)

lift_definition lvalue_pair :: "('mem,'val1) lvalue \<Rightarrow> ('mem,'val2) lvalue \<Rightarrow> ('mem,'val1\<times>'val2) lvalue" is
  \<open>\<lambda>x y. case (x,y) of (Some x, Some y) \<Rightarrow> 
    if LValues.compatible_lvalues x y then Some (LValues.lvalue_pair x y) else None
    | _ \<Rightarrow> None\<close>
  apply (rename_tac x y; case_tac x; case_tac y)
  by auto

abbreviation compatible_lvalues where
  "compatible_lvalues x y \<equiv> valid_lvalue (lvalue_pair x y)"

lemma compatible_valid1: "compatible_lvalues x y \<Longrightarrow> valid_lvalue x"
  apply transfer apply (rename_tac x y; case_tac x) by auto

lemma compatible_valid2: "compatible_lvalues x y \<Longrightarrow> valid_lvalue y"
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
  apply auto
  by (metis get_set_diff iso_tuple_UNIV_I option.distinct(1))

lift_definition unit_lvalue :: "('mem,unit) lvalue" is "Some (LValues.unit_lvalue UNIV)"
  by auto

lemma valid_unit_lvalue[simp]: "valid_lvalue unit_lvalue"
  apply transfer by simp

lemma unit_setter[simp]: "setter unit_lvalue x = id"
  apply transfer by simp

lemma unit_lvalue_compat[simp]:
  assumes [simp]: "valid_lvalue x"
  shows "compatible_lvalues unit_lvalue x"
  using assms apply transfer by auto

lemma unit_lvalue_compat'[simp]:
  assumes [simp]: "valid_lvalue x"
  shows "compatible_lvalues x unit_lvalue"
  using assms apply transfer by auto

lift_definition mk_lvalue :: "('mem\<Rightarrow>'val) \<Rightarrow> ('val\<Rightarrow>'mem\<Rightarrow>'mem) \<Rightarrow> ('mem,'val) lvalue" is
  "\<lambda>g s. let x = \<lparr> lv_domain=UNIV, lv_range=UNIV, lv_getter=g, lv_setter=s \<rparr> in
    if LValues.valid_lvalue x then Some x else None"
  by (smt option.simps(4) option.simps(5) select_convs(1) select_convs(2))
  

lemma mk_lvalue_valid:
  assumes [simp]: "\<And>a m. g (s a m) = a"
  assumes [simp]: "\<And>m. s (g m) m = m"
  assumes [simp]: "\<And>a b m. s a (s b m) = s a m"
  shows "valid_lvalue (mk_lvalue g s)"
  apply (transfer fixing: g s) apply (simp add: Let_def)
  apply (rule valid_lvalueI)
  by auto

lemma getter_mk_lvalue[simp]:
  assumes "valid_lvalue (mk_lvalue g s)"
  shows "getter (mk_lvalue g s) = g"
  using assms apply transfer by (auto simp: Let_def)

lemma setter_mk_lvalue[simp]:
  assumes "valid_lvalue (mk_lvalue g s)"
  shows "setter (mk_lvalue g s) = s"
  using assms apply transfer by (auto simp: Let_def)

lemma mk_lvalue_compat:
  assumes "valid_lvalue (mk_lvalue g s)"
  assumes "valid_lvalue (mk_lvalue g' s')"
  assumes [simp]: "\<And>a b m. s a (s' b m) = s' b (s a m)"
  shows "compatible_lvalues (mk_lvalue g s) (mk_lvalue g' s')"
  using assms(1,2) apply (transfer fixing: g s g' s')
  apply (auto simp: Let_def)
  apply (meson option.distinct(1))
  apply (meson option.distinct(1))
  apply (rule LValues.compatible_lvalues.intros)
  apply auto
  apply (meson option.distinct(1))
  by (meson option.distinct(1))

lemma setter_pair [simp]:
  assumes "compatible_lvalues x y"
  shows "setter (lvalue_pair x y) (a,b) m = setter y b (setter x a m)"
  using assms apply (transfer fixing: m a b)
  apply (rename_tac x y; case_tac x; case_tac y)
  by auto

lemma setter_pair':
  assumes "compatible_lvalues x y"
  shows "setter (lvalue_pair x y) ab m = setter y (snd ab) (setter x (fst ab) m)"
  by (metis LValues_Typed.setter_pair assms prod.exhaust_sel)

lift_definition fst_lvalue :: "('a*'b, 'a) lvalue" is
  "Some \<lparr> lv_domain=UNIV, lv_range=UNIV, lv_getter=fst, lv_setter=\<lambda>a (_,b). (a,b) \<rparr>"
  apply auto apply (rule valid_lvalueI) by auto

lift_definition snd_lvalue :: "('a*'b, 'b) lvalue" is
  "Some \<lparr> lv_domain=UNIV, lv_range=UNIV, lv_getter=snd, lv_setter=\<lambda>b (a,_). (a,b) \<rparr>"
  apply auto apply (rule valid_lvalueI) by auto

lemma valid_fst[simp]: "valid_lvalue fst_lvalue"
  apply transfer by simp

lemma valid_snd[simp]: "valid_lvalue snd_lvalue"
  apply transfer by simp

lemma compat_fst_snd[simp]: "compatible_lvalues fst_lvalue snd_lvalue"
  apply transfer apply auto
  apply (rule compatible_lvalues.intros)
     apply auto 
   apply (rule valid_lvalueI; auto)
  by (rule valid_lvalueI; auto)

lift_definition function_lvalue :: "'a \<Rightarrow> ('a\<Rightarrow>'b, 'b) lvalue" is
  "\<lambda>i. Some \<lparr> lv_domain=UNIV, lv_range=UNIV, lv_getter=\<lambda>m. m i, lv_setter=\<lambda>a m. m(i:=a) \<rparr>"
  apply auto apply (rule valid_lvalueI) by auto

lemma valid_function_lvalue[simp]: "valid_lvalue (function_lvalue a)"
  apply transfer by auto

lemma compat_function_lvalue[simp]: "x \<noteq> y \<Longrightarrow> compatible_lvalues (function_lvalue x) (function_lvalue y)"
  apply (transfer fixing: x y) apply auto
  apply (rule compatible_lvalues.intros)
     apply auto
   apply (rule valid_lvalueI) apply auto
  apply (rule valid_lvalueI) by auto


lemma fst_split_memory[simp]: 
  assumes "valid_lvalue x"
  shows "fst (split_memory x m) = getter x m"
  using assms apply transfer by auto

lemma split_pair_eq_typed:
  fixes x y
  assumes [simp]: "compatible_lvalues x y"
  defines "xy \<equiv> lvalue_pair x y"
  shows "snd (split_memory x m1) = snd (split_memory x m2)
     \<longleftrightarrow> snd (split_memory xy m1) = snd (split_memory xy m2)
         \<and> getter y m1 = getter y m2"
  unfolding xy_def using assms(1)
  apply (transfer fixing: m1 m2)
  apply (rename_tac x y; case_tac x; case_tac y)
     apply simp_all
  apply (subst split_pair_eq)
  apply auto
  by (meson option.distinct(1))



nonterminal lvalue_expr
nonterminal lvalue_expr_chain
nonterminal lvalue_expr_atom

syntax "" :: "id \<Rightarrow> lvalue_expr_atom" ("_")
syntax "" :: "lvalue_expr \<Rightarrow> lvalue_expr_atom" ("'(_')")

(* syntax "" :: "lvalue_expr_atom \<Rightarrow> lvalue_expr_indexed" ("_") *)
(* syntax "lvalue_index" :: "lvalue_expr_atom \<Rightarrow> 'a \<Rightarrow> lvalue_expr_indexed" ("_[_]") *)

syntax "" :: "lvalue_expr_atom \<Rightarrow> lvalue_expr_chain" ("_")
syntax "_lvalue_index" :: "lvalue_expr_chain \<Rightarrow> 'a \<Rightarrow> lvalue_expr_chain" ("_[_]")
syntax "lvalue_chain" :: "lvalue_expr_chain \<Rightarrow> lvalue_expr_atom \<Rightarrow> lvalue_expr_chain" (infixl "\<rightarrow>" 90)

syntax "" :: "lvalue_expr_chain \<Rightarrow> lvalue_expr" ("_")
syntax "lvalue_pair" :: "lvalue_expr_chain \<Rightarrow> lvalue_expr \<Rightarrow> lvalue_expr" (infixr "," 80)
syntax "_lvalue_expr" :: "lvalue_expr \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>")

(* translations "_lvalue_id x" \<rightharpoonup> "x" *)
(* translations "_lvalue_paren x" \<rightharpoonup> "x" *)
(* translations "_lvalue_pair x y" \<rightharpoonup> "CONST lvalue_pair x y" *)
translations "_lvalue_index x i" \<rightharpoonup> "CONST lvalue_chain x (CONST function_lvalue i)"
translations "_lvalue_expr x" \<rightharpoonup> "x :: (_,_) lvalue"
(* translations "_lvalue_chain x y" \<rightharpoonup> "CONST lvalue_chain x y" *)

term "\<lbrakk>x[3]\<rbrakk>"
term "\<lbrakk>x\<rightarrow>fst_lvalue, y\<rbrakk>"
term "\<lbrakk>(x,z)\<rightarrow>x, y\<rbrakk>"


end
