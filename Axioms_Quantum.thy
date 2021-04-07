section \<open>Quantum instantiation of lvalues\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Quantum.thy)

    # Type classe
    domain \<rightarrow> finite
    
    # Constants
    comp_update \<rightarrow> timesOp
    id_update \<rightarrow> idOp
    update_hom \<rightarrow> clinear
    update_2hom \<rightarrow> cbilinear
    tensor_update \<rightarrow> tensor_op
    
    # Lemmas
    id_update_left \<rightarrow> times_idOp2
    id_update_right \<rightarrow> times_idOp1
    comp_update_assoc \<rightarrow> cblinfun_apply_assoc
    id_update_hom \<rightarrow> complex_vector.linear_id
    comp_update_hom \<rightarrow> Complex_Vector_Spaces.linear_compose
    comp_update_is_2hom \<rightarrow> cbilinear_timesOp
    tensor_update_mult \<rightarrow> comp_tensor_op
    tensor_update_is_2hom \<rightarrow> tensor_op_cbilinear

    # Chapter name
    Generic laws about lvalues \<rightarrow> Generic laws about lvalues, instantiated quantumly
*)

theory Axioms_Quantum
  imports Jordan_Normal_Form.Matrix_Impl "HOL-Library.Rewrite"
          Bounded_Operators.Complex_L2
          Finite_Tensor_Product
begin


unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)

type_synonym 'a update = \<open>('a ell2, 'a ell2) cblinfun\<close>

lemma update_hom_o_2hom_is_2hom: \<open>cbilinear F2 \<Longrightarrow> clinear G \<Longrightarrow> cbilinear (\<lambda>a b. G (F2 a b))\<close>
  apply (auto simp: cbilinear_def intro!: clinearI)
  apply (smt (z3) clinear_additive_D)
  apply (metis complex_vector.linear_scale)
   apply (simp add: clinear_additive_D)
  by (simp add: complex_vector.linear_scale)
lemma update_2hom_o_hom_left_is_hom: \<open>cbilinear F2 \<Longrightarrow> clinear G \<Longrightarrow> cbilinear (\<lambda>a b. F2 (G a) b)\<close>
  apply (auto simp: cbilinear_def intro!: clinearI)
  apply (smt (z3) clinear_additive_D)
  by (metis (full_types) complex_vector.linear_scale)
lemma update_2hom_sym: \<open>cbilinear F2 \<Longrightarrow> cbilinear (\<lambda>a b. F2 b a)\<close> 
  by (auto simp: cbilinear_def)
lemma update_2hom_left_is_hom: \<open>cbilinear F2 \<Longrightarrow> clinear (\<lambda>a. F2 a b)\<close>
  by (auto simp: cbilinear_def)

definition lvalue :: \<open>('a::finite update \<Rightarrow> 'b::finite update) \<Rightarrow> bool\<close> where
  "lvalue F \<longleftrightarrow> 
     clinear F
   \<and> F idOp = idOp 
   \<and> (\<forall>a b. F(a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b)
   \<and> (\<forall>a. F (a*) = (F a)*)"

lemma lvalue_of_id: \<open>lvalue F \<Longrightarrow> F idOp = idOp\<close>
  by (simp add: lvalue_def)

lemma lvalue_hom: "lvalue F \<Longrightarrow> clinear F"
  unfolding lvalue_def by simp

lemma lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"
  unfolding lvalue_def
  apply auto
  using Complex_Vector_Spaces.linear_compose by blast

lemma lvalue_mult: "lvalue F \<Longrightarrow> timesOp (F a) (F b) = F (timesOp a b)"
  unfolding lvalue_def
  by auto

lemma lvalue_tensor_left: \<open>lvalue (\<lambda>a. tensor_op a idOp)\<close>
  by (simp add: comp_tensor_op lvalue_def update_2hom_left_is_hom tensor_op_cbilinear tensor_op_adjoint)

lemma lvalue_tensor_right: \<open>lvalue (\<lambda>a. tensor_op idOp a)\<close>
  apply (simp add: comp_tensor_op lvalue_def tensor_op_cbilinear tensor_op_adjoint)
  by (meson cbilinear_def tensor_op_cbilinear)

lemma pair_lvalue_axiom: 
  fixes F :: \<open>'a::finite update \<Rightarrow> 'c::finite update\<close> and G :: \<open>'b::finite update \<Rightarrow> 'c update\<close>
  assumes \<open>lvalue F\<close> and \<open>lvalue G\<close> and [simp]: \<open>clinear p\<close>
  assumes compat: \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  assumes tensor: \<open>\<And>a b. p (tensor_op a b) = F a o\<^sub>C\<^sub>L G b\<close>
  shows \<open>lvalue p\<close>
proof (unfold lvalue_def, intro conjI allI)
  have h1: \<open>clinear (\<lambda>a. p (a o\<^sub>C\<^sub>L b))\<close> for b :: "('a \<times> 'b) update"
    apply (rule linear_compose[unfolded o_def, of _ p])
     apply (simp add: cblinfun_apply_dist1 clinearI)
    by simp
  have h2: \<open>clinear (\<lambda>a. p a o\<^sub>C\<^sub>L p b)\<close> for b
    apply (rule linear_compose[unfolded o_def, of p])
    apply simp
    by (meson cblinfun_apply_dist1 clinearI scalar_op_op)
  have h3: \<open>clinear (\<lambda>c. p (d o\<^sub>C\<^sub>L c))\<close> for d :: "('a \<times> 'b) update"
    apply (rule linear_compose[unfolded o_def, of _ p])
     apply (simp add: cblinfun_apply_dist2 clinearI)
    by simp
  have h4: \<open>clinear (\<lambda>c. p d o\<^sub>C\<^sub>L p c)\<close> for d
    apply (rule linear_compose[unfolded o_def, of p])
    apply simp
    by (simp add: cblinfun_apply_dist2 clinearI)

  fix x y :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  show "clinear p"
    using assms by auto
  show \<open>p idOp = idOp\<close>
    unfolding tensor_id[symmetric] tensor
    using \<open>lvalue F\<close> \<open>lvalue G\<close> unfolding lvalue_def by auto

  have *: \<open>p (tensor_op a b o\<^sub>C\<^sub>L tensor_op a' b') = p (tensor_op a b) o\<^sub>C\<^sub>L p (tensor_op a' b')\<close> for a b a' b'
    using \<open>lvalue F\<close> \<open>lvalue G\<close>
    apply (simp add: tensor comp_tensor_op lvalue_def)
    by (metis cblinfun_apply_assoc compat)
  show \<open>p (x o\<^sub>C\<^sub>L y) = p x o\<^sub>C\<^sub>L p y\<close>
    using h1 h2 apply (rule tensor_extensionality[THEN fun_cong, where x=x])
    using h3 h4 apply (rule tensor_extensionality[THEN fun_cong, where x=y])
    using * by -

  have hom_padjadj: \<open>clinear (\<lambda>a. p (a*)*)\<close>
    using \<open>clinear p\<close>
    by (auto simp: Adj_cblinfun_plus complex_vector.linear_add complex_vector.linear_scale intro!: clinearI)

  have *: \<open>(p (tensor_op a b*))* = p (tensor_op a b)\<close> for a b
    using \<open>lvalue F\<close> \<open>lvalue G\<close>
    by (simp add: compat tensor tensor_op_adjoint lvalue_def)
  have \<open>(p (x*))* = p x\<close>
    apply (rule fun_cong[where x=x])
    apply (rule tensor_extensionality)
    using hom_padjadj * by simp_all
  then show \<open>p (x*) = (p x)*\<close>
    by (metis adjoint_twice)
qed

end
