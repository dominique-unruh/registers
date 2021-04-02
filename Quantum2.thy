theory Quantum2
  imports
    LawsAdj_Quantum
    Bounded_Operators.Bounded_Operators_Code
    Real_Impl.Real_Impl
    "HOL-Library.Code_Target_Numeral"
    Quantum
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle lvalue_notation
unbundle cblinfun_notation

lemma lvalue_id[simp]: \<open>lvalue (\<lambda>x. x)\<close>
  by (metis (mono_tags, lifting) complex_vector.module_hom_ident lvalue_def)

lemma lvalue_projector:
  assumes "lvalue F"
  assumes "isProjector a"
  shows "isProjector (F a)"
  using assms unfolding lvalue_def isProjector_algebraic by metis

lemma compatible_proj_intersect:
  (* I think this also holds without isProjector, but my proof idea uses the Penrose-Moore 
     pseudoinverse and we do not have an existence theorem for it. *)
  assumes "compatible R S" and "isProjector a" and "isProjector b"
  shows "(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) = ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)"
proof (rule antisym)
  have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (S b *\<^sub>S \<top>)"
    apply (subst swap_lvalues[OF assms(1)])
    by (auto simp: cblinfun_apply_assoc_subspace intro!: applyOpSpace_mono)
  moreover have "((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>)"
    by (auto simp: cblinfun_apply_assoc_subspace intro!: applyOpSpace_mono)
  ultimately show \<open>((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>) \<le> (R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>)\<close>
    by auto

  have "isProjector (R a)"
    using assms(1) assms(2) compatible_lvalue1 lvalue_projector by blast
  have "isProjector (S b)"
    using assms(1) assms(3) compatible_lvalue2 lvalue_projector by blast
  show \<open>(R a *\<^sub>S \<top>) \<sqinter> (S b *\<^sub>S \<top>) \<le> (R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>\<close>
  proof (unfold less_eq_clinear_space.rep_eq, rule)
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
      by simp
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
  apply (metis (no_types, lifting) cblinfun_apply_assoc lvalue_mult)
  by (simp add: assms(2) assms(3) isProjector_D2 lvalue_projector)

lemma sandwich_tensor: "sandwich (a \<otimes>\<^sub>o b) = sandwich a \<otimes>\<^sub>h sandwich b"
  for a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
  apply (rule tensor_extensionality)
  by (auto simp: sandwich_def tensor_update_hom_is_hom comp_tensor_op tensor_op_adjoint)

lemma sandwich_grow_left: "sandwich a \<otimes>\<^sub>h id = sandwich (a \<otimes>\<^sub>o idOp)"
  for a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
    by (simp add: sandwich_tensor sandwich_id)

lemma lvalue_sandwich: \<open>lvalue F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) lvalue_def sandwich_def)

lemma unitary_sandwich_lvalue: \<open>unitary a \<Longrightarrow> lvalue (sandwich a)\<close>
  unfolding lvalue_def sandwich_def
  by (smt (z3) adjoint_twice assoc_left(1) cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI op_scalar_op scalar_op_op times_adjoint times_idOp2 unitary_def)

lemma assoc_ell2_sandwich: \<open>assoc = sandwich assoc_ell2\<close>
  unfolding sandwich_def
  apply (rule tensor_extensionality3')
    apply simp
   apply (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: assoc_apply times_applyOp tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor
           flip: tensor_ell2_ket)

lemma assoc_ell2'_sandwich: \<open>assoc' = sandwich assoc_ell2'\<close>
  unfolding sandwich_def
  apply (rule tensor_extensionality3)
    apply simp
   apply (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: assoc'_apply times_applyOp tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor 
           flip: tensor_ell2_ket)

lemma swap_sandwich: "swap = sandwich Uswap"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_def)
  apply (rule tensor_ell2_extensionality)
  by (simp add: times_applyOp tensor_op_ell2)

lemma id_tensor_sandwich: 
  fixes a :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2"
  shows "id \<otimes>\<^sub>h sandwich a = sandwich (idOp \<otimes>\<^sub>o a)"
  apply (rule tensor_extensionality) 
  by (simp_all add: tensor_update_hom_is_hom comp_tensor_op sandwich_def tensor_op_adjoint)

lemma mat_of_cblinfun_sandwich: 
  fixes a :: "(_::onb_enum, _::onb_enum) cblinfun"
  shows \<open>mat_of_cblinfun (sandwich a b) = (let a' = mat_of_cblinfun a in a' * mat_of_cblinfun b * mat_adjoint a')\<close>
  by (simp add: cblinfun_of_mat_timesOp sandwich_def Let_def mat_of_cblinfun_adjoint')

end

