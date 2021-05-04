section \<open>Quantum instantiation of lvalues\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Quantum.thy)

    # Type classes
    domain \<rightarrow> finite
    
    # Constants
    comp_update \<rightarrow> timesOp
    id_update \<rightarrow> idOp
    update_hom \<rightarrow> clinear
    tensor_update \<rightarrow> tensor_op
    
    # Lemmas
    id_update_left \<rightarrow> times_idOp2
    id_update_right \<rightarrow> times_idOp1
    comp_update_assoc \<rightarrow> cblinfun_apply_assoc
    id_update_hom \<rightarrow> complex_vector.linear_id
    comp_update_hom \<rightarrow> clinear_compose
    tensor_update_mult \<rightarrow> comp_tensor_op
    update_hom_tensor_left_is_hom \<rightarrow> clinear_tensor_right
    update_hom_tensor_right_is_hom \<rightarrow> clinear_tensor_left

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

(* lemma update_hom_o_2hom_is_2hom: \<open>cbilinear F2 \<Longrightarrow> clinear G \<Longrightarrow> cbilinear (\<lambda>a b. G (F2 a b))\<close>
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
  by (auto simp: cbilinear_def) *)

lemma update_hom_mult_right: \<open>clinear (\<lambda>a. a o\<^sub>C\<^sub>L z)\<close>
  by (simp add: cblinfun_apply_dist1 clinearI)
lemma update_hom_mult_left: \<open>clinear (\<lambda>a. z o\<^sub>C\<^sub>L a)\<close>
  by (simp add: cblinfun_apply_dist2 clinearI)

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
  using clinear_compose by blast

lemma lvalue_mult: "lvalue F \<Longrightarrow> timesOp (F a) (F b) = F (timesOp a b)"
  unfolding lvalue_def
  by auto

lemma lvalue_tensor_left: \<open>lvalue (\<lambda>a. tensor_op a idOp)\<close>
  by (simp add: comp_tensor_op lvalue_def tensor_op_cbilinear tensor_op_adjoint)

lemma lvalue_tensor_right: \<open>lvalue (\<lambda>a. tensor_op idOp a)\<close>
  by (simp add: comp_tensor_op lvalue_def tensor_op_cbilinear tensor_op_adjoint)


definition lvalue_pair ::
  \<open>('a::finite update \<Rightarrow> 'c::finite update) \<Rightarrow> ('b::finite update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  \<open>lvalue_pair F G = tensor_lift (\<lambda>a b. F a o\<^sub>C\<^sub>L G b)\<close>

lemma cbilinear_F_comp_G[simp]: \<open>clinear F \<Longrightarrow> clinear G \<Longrightarrow> cbilinear (\<lambda>a b. F a o\<^sub>C\<^sub>L G b)\<close>
  unfolding cbilinear_def
  by (auto simp add: clinear_iff cblinfun_apply_dist1 cblinfun_apply_dist2)

lemma lvalue_pair_apply: 
  assumes \<open>lvalue F\<close> and \<open>lvalue G\<close>
  assumes \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  shows \<open>(lvalue_pair F G) (tensor_op a b) = F a o\<^sub>C\<^sub>L G b\<close>
  unfolding lvalue_pair_def
  apply (subst tensor_lift_correct[THEN fun_cong, THEN fun_cong])
  apply (rule cbilinear_F_comp_G)
  using assms apply (auto intro!: cbilinear_F_comp_G)
  using lvalue_def by auto

lemma lvalue_pair_lvalue:
  fixes F :: \<open>'a::finite update \<Rightarrow> 'c::finite update\<close> and G
  assumes [simp]: \<open>lvalue F\<close> and [simp]: \<open>lvalue G\<close>
  assumes \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  shows \<open>lvalue (lvalue_pair F G)\<close> 
proof (unfold lvalue_def, intro conjI allI)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    using assms lvalue_def by blast+
  have [simp]: \<open>F idOp = idOp\<close> \<open>G idOp = idOp\<close>
    using assms(1,2) lvalue_def by blast+
  show [simp]: \<open>clinear (lvalue_pair F G)\<close>
    unfolding lvalue_pair_def apply (rule tensor_lift_hom)
    by simp
  show \<open>lvalue_pair F G idOp = idOp\<close>
    apply (simp flip: tensor_id)
    apply (subst lvalue_pair_apply)
    using assms by simp_all
  have [simp]: \<open>clinear (\<lambda>y. lvalue_pair F G (x o\<^sub>C\<^sub>L y))\<close> for x :: \<open>('a\<times>'b) update\<close>
    apply (rule clinear_compose[unfolded o_def, where g=\<open>lvalue_pair F G\<close>])
    by (simp_all add: cblinfun_apply_dist2 clinearI)
  have [simp]: \<open>clinear (\<lambda>y. x o\<^sub>C\<^sub>L lvalue_pair F G y)\<close> for x :: \<open>'c update\<close>
    apply (rule clinear_compose[unfolded o_def, where f=\<open>lvalue_pair F G\<close>])
    by (simp_all add: cblinfun_apply_dist2 clinearI)
  have [simp]: \<open>clinear (\<lambda>x. lvalue_pair F G (x o\<^sub>C\<^sub>L y))\<close> for y :: \<open>('a\<times>'b) update\<close>
    apply (rule clinear_compose[unfolded o_def, where g=\<open>lvalue_pair F G\<close>])
    by (simp_all add: cblinfun_apply_dist1 clinearI)
  have [simp]: \<open>clinear (\<lambda>x. lvalue_pair F G x o\<^sub>C\<^sub>L y)\<close> for y :: \<open>'c update\<close>
    apply (rule clinear_compose[unfolded o_def, where f=\<open>lvalue_pair F G\<close>])
    by (simp_all add: cblinfun_apply_dist1 clinearI)
  have [simp]: \<open>F (x o\<^sub>C\<^sub>L y) = F x o\<^sub>C\<^sub>L F y\<close> for x y
    by (simp add: lvalue_mult)
  have [simp]: \<open>G (x o\<^sub>C\<^sub>L y) = G x o\<^sub>C\<^sub>L G y\<close> for x y
    by (simp add: lvalue_mult)
  have [simp]: \<open>clinear (\<lambda>a. (lvalue_pair F G (a*))*)\<close>
    apply (rule antilinear_o_antilinear[unfolded o_def, where f=\<open>adj\<close>])
     apply (simp add: Adj_cblinfun_plus antilinearI)
    apply (rule antilinear_o_clinear[unfolded o_def, where g=\<open>adj\<close>])
    by (simp_all add: Adj_cblinfun_plus antilinearI)
  have [simp]: \<open>F (a*) = (F a)*\<close> for a
    using assms(1) lvalue_def by blast
  have [simp]: \<open>G (b*) = (G b)*\<close> for b
    using assms(2) lvalue_def by blast

  fix a b
  show \<open>lvalue_pair F G (a o\<^sub>C\<^sub>L b) = lvalue_pair F G a o\<^sub>C\<^sub>L lvalue_pair F G b\<close>
    apply (rule tensor_extensionality[THEN fun_cong, where x=b], simp_all)
    apply (rule tensor_extensionality[THEN fun_cong, where x=a], simp_all)
    apply (simp_all add: comp_tensor_op lvalue_pair_apply assms(3))
    using assms(3) by (metis assoc_left(1)) 
  have \<open>(lvalue_pair F G (a*))* = lvalue_pair F G a\<close>
    apply (rule tensor_extensionality[THEN fun_cong, where x=a])
    by (simp_all add: tensor_op_adjoint lvalue_pair_apply assms(3))
  then show \<open>lvalue_pair F G (a*) = lvalue_pair F G a*\<close>
    by (metis adjoint_twice)
qed


(* lemma pair_lvalue_axiom: 
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

  have hom_padjadj: \<open>clinear (\<lambda>a. p (a* )* )\<close>
    using \<open>clinear p\<close>
    by (auto simp: Adj_cblinfun_plus complex_vector.linear_add complex_vector.linear_scale intro!: clinearI)

  have *: \<open>(p (tensor_op a b* ))* = p (tensor_op a b)\<close> for a b
    using \<open>lvalue F\<close> \<open>lvalue G\<close>
    by (simp add: compat tensor tensor_op_adjoint lvalue_def)
  have \<open>(p (x* ))* = p x\<close>
    apply (rule fun_cong[where x=x])
    apply (rule tensor_extensionality)
    using hom_padjadj * by simp_all
  then show \<open>p (x* ) = (p x)*\<close>
    by (metis adjoint_twice)
qed *)

end
