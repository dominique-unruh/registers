section \<open>Derived facts about quantum registers\<close>

theory Quantum_Extra
  imports
    Laws_Quantum
    Bounded_Operators.Bounded_Operators_Code
    Real_Impl.Real_Impl
    "HOL-Library.Code_Target_Numeral"
    Quantum
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle register_notation
unbundle cblinfun_notation

lemma register_id[simp]: \<open>register (\<lambda>x. x)\<close>
  by (metis (mono_tags, lifting) complex_vector.module_hom_ident register_def)

lemma register_id'[simp]: \<open>register id\<close>
  by (simp add: id_def)

lemma register_projector:
  assumes "register F"
  assumes "isProjector a"
  shows "isProjector (F a)"
  using assms unfolding register_def isProjector_algebraic by metis

lemma register_unitary:
  assumes "register F"
  assumes "unitary a"
  shows "unitary (F a)"
  using assms by (smt (verit, best) register_def unitary_def)

lemma compatible_proj_intersect:
  (* I think this also holds without isProjector, but my proof idea uses the Penrose-Moore 
     pseudoinverse or simultaneous diagonalization and we do not have an existence theorem for it. *)
  assumes "compatible R S" and "isProjector a" and "isProjector b"
  shows "(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) = ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)"
proof (rule antisym)
  have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (S b *\<^sub>S \<top>)"
    apply (subst swap_registers[OF assms(1)])
    by (auto simp: cblinfun_apply_assoc_subspace intro!: applyOpSpace_mono)
  moreover have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>)"
    by (auto simp: cblinfun_apply_assoc_subspace intro!: applyOpSpace_mono)
  ultimately show \<open>((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>)\<close>
    by auto

  have "isProjector (R a)"
    using assms(1) assms(2) compatible_register1 register_projector by blast
  have "isProjector (S b)"
    using assms(1) assms(3) compatible_register2 register_projector by blast
  show \<open>(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) \<le> (R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>\<close>
  proof (unfold less_eq_ccsubspace.rep_eq, rule)
    fix \<psi>
    assume asm: \<open>\<psi> \<in> space_as_set ((R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>))\<close>
    then have \<open>\<psi> \<in> space_as_set (R a *\<^sub>S \<top>)\<close>
      by auto
    then have R: \<open>R a *\<^sub>V \<psi> = \<psi>\<close>
      using \<open>isProjector (R a)\<close> apply_left_neutral isProjector_algebraic by blast
    from asm have \<open>\<psi> \<in> space_as_set (S b *\<^sub>S \<top>)\<close>
      by auto
    then have S: \<open>S b *\<^sub>V \<psi> = \<psi>\<close>
      using \<open>isProjector (S b)\<close> apply_left_neutral isProjector_algebraic by blast
    from R S have \<open>\<psi> = (R a o\<^sub>C\<^sub>L S b) *\<^sub>V \<psi>\<close>
      by (simp add: times_applyOp)
    also have \<open>\<dots> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      apply simp by (metis R S calculation cblinfun_apply_in_image)
    finally show \<open>\<psi> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      by -
  qed
qed

lemma compatible_proj_mult:
  assumes "compatible R S" and "isProjector a" and "isProjector b"
  shows "isProjector (R a o\<^sub>C\<^sub>L S b)"
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  using assms unfolding isProjector_algebraic compatible_def
  apply auto
  apply (metis (no_types, lifting) cblinfun_apply_assoc register_mult)
  by (simp add: assms(2) assms(3) isProjector_D2 register_projector)

lemma unitary_sandwich_register: \<open>unitary a \<Longrightarrow> register (sandwich a)\<close>
  unfolding register_def sandwich_def
  by (smt (z3) adjoint_twice assoc_left(1) cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI op_scalar_op scalar_op_op times_adjoint times_idOp2 unitary_def)

lemma sandwich_tensor: 
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
  assumes \<open>unitary a\<close> \<open>unitary b\<close>
  shows "sandwich (a \<otimes>\<^sub>o b) = sandwich a \<otimes>\<^sub>r sandwich b"
  apply (rule tensor_extensionality)
  by (auto simp: unitary_sandwich_register assms sandwich_def register_tensor_is_hom comp_tensor_op tensor_op_adjoint)

lemma sandwich_grow_left: 
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assumes "unitary a"
  shows "sandwich a \<otimes>\<^sub>r id = sandwich (a \<otimes>\<^sub>o idOp)"
  by (simp add: unitary_sandwich_register assms sandwich_tensor sandwich_id)

lemma register_sandwich: \<open>register F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) register_def sandwich_def)

lemma assoc_ell2_sandwich: \<open>assoc = sandwich assoc_ell2\<close>
  apply (rule tensor_extensionality3')
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_def assoc_apply times_applyOp tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor
           flip: tensor_ell2_ket)

lemma assoc_ell2'_sandwich: \<open>assoc' = sandwich assoc_ell2'\<close>
  apply (rule tensor_extensionality3)
    apply (simp_all add: unitary_sandwich_register)[2]
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: sandwich_def assoc'_apply times_applyOp tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor 
           flip: tensor_ell2_ket)

lemma swap_sandwich: "swap = sandwich Uswap"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_def)[2]
  apply (rule tensor_ell2_extensionality)
  by (simp add: sandwich_def times_applyOp tensor_op_ell2)

lemma id_tensor_sandwich: 
  fixes a :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2"
  assumes "unitary a"
  shows "id \<otimes>\<^sub>r sandwich a = sandwich (idOp \<otimes>\<^sub>o a)"
  apply (rule tensor_extensionality) 
  using assms by (auto simp: register_tensor_is_hom comp_tensor_op sandwich_def tensor_op_adjoint unitary_sandwich_register)

lemma compatible_selfbutter_join:
  assumes [compatible]: "compatible R S"
  shows "R (selfbutter \<psi>) o\<^sub>C\<^sub>L S (selfbutter \<phi>) = (R; S) (selfbutter (\<psi> \<otimes>\<^sub>s \<phi>))"
  apply (subst register_pair_apply[symmetric, where F=R and G=S])
  using assms by auto

definition empty_var :: \<open>'a::{CARD_1,enum} update \<Rightarrow> 'b::finite update\<close> where
  "empty_var a = one_dim_iso a *\<^sub>C idOp"

lemma register_empty_var[simp]: \<open>register empty_var\<close>
  unfolding register_def empty_var_def
  by (auto simp add: clinearI scaleC_left.add)

lemma empty_var_compatible[simp]: \<open>register X \<Longrightarrow> compatible empty_var X\<close>
  apply (rule compatibleI)
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  by (auto simp: empty_var_def)

lemma empty_var_compatible'[simp]: \<open>register X \<Longrightarrow> compatible X empty_var\<close>
  using compatible_sym empty_var_compatible by blast

end

