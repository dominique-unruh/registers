theory Quantum2
  imports Laws_Quantum "HOL-ex.Bit_Lists" "HOL-Library.Z2"
    Bounded_Operators.Bounded_Operators_Code
    Real_Impl.Real_Impl
    "HOL-Library.Code_Target_Numeral"
    Quantum
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
unbundle lvalue_notation
unbundle cblinfun_notation

declare lvalue_hom[simp]

lemma pair_comp_tensor':
  assumes "compatible A B" and \<open>clinear C\<close> and \<open>clinear D\<close>
  shows "(pair A B) ((C \<otimes>\<^sub>h D) x) = (pair (A o C) (B o D)) x"
  using pair_comp_tensor[OF assms]
  by (smt (z3) fcomp_comp fcomp_def)

lemma pair_comp_swap':
  assumes "compatible A B"
  shows "(pair A B) (swap x) = pair B A x"
  using pair_comp_swap[OF assms]
  by (metis comp_def)

(* TODO Laws *)
lemma lvalue_of_id[simp]: \<open>lvalue R \<Longrightarrow> R idOp = idOp\<close>
  by (auto simp: lvalue_def)

lemma lvalue_comp'1[simp]: \<open>lvalue R \<Longrightarrow> R A o\<^sub>C\<^sub>L (R B o\<^sub>C\<^sub>L C) = R (A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
  by (metis (no_types, lifting) assoc_left(1) lvalue_mult)

lemma lvalue_left_idOp[intro!]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a. idOp \<otimes> F a)\<close>
  using assms unfolding lvalue_def 
  apply auto
  using left_tensor_hom[of idOp] linear_compose[of F \<open>\<lambda>x. idOp \<otimes> x\<close>, unfolded o_def] o_def
  apply (smt (z3))
  apply (metis (no_types, hide_lams) comp_tensor_op times_idOp2)
  by (metis (full_types) idOp_adjoint tensor_op_adjoint)

lemma lvalue_right_idOp[intro!]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a. F a \<otimes> idOp)\<close>
  using assms unfolding lvalue_def 
  apply auto
  using right_tensor_hom[of idOp] linear_compose[of F \<open>\<lambda>x. x \<otimes> idOp\<close>, unfolded o_def] o_def
  apply (smt (z3))
  apply (metis (no_types, hide_lams) comp_tensor_op times_idOp2)
  by (metis (full_types) idOp_adjoint tensor_op_adjoint)

lemma lvalue_id'[simp]: \<open>lvalue (\<lambda>x. x)\<close>
  by (metis (mono_tags, lifting) complex_vector.module_hom_ident lvalue_def)

lemma compatible_left_idOp[intro!]:
  assumes "compatible F G"
  shows "compatible (\<lambda>a. idOp \<otimes> F a) (\<lambda>a. idOp \<otimes> G a)"
  using assms unfolding compatible_def apply auto
  by (metis comp_tensor_op)

lemma compatible_left_idOp1[intro!]:
  assumes "lvalue F" and "lvalue G"
  shows "compatible (\<lambda>a. F a \<otimes> idOp) (\<lambda>a. idOp \<otimes> G a)"
  using assms unfolding compatible_def apply auto
  by (metis (no_types, hide_lams) comp_tensor_op times_idOp1 times_idOp2)

lemma compatible_left_idOp2[intro!]:
  assumes "lvalue F" and "lvalue G"
  shows "compatible (\<lambda>a. idOp \<otimes> F a) (\<lambda>a. G a \<otimes> idOp)"
  using assms unfolding compatible_def apply auto
  by (metis (no_types, hide_lams) comp_tensor_op times_idOp1 times_idOp2)

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
      (* TODO: There should a theorem for this in the bounded operator library. *)
      apply transfer
      by (meson closure_subset range_eqI subsetD)
    finally show \<open>\<psi> \<in> space_as_set ((R a o\<^sub>C\<^sub>L S b) *\<^sub>S \<top>)\<close>
      by -
  qed
qed

lemma compatible_proj_mult:
  assumes "compatible R S" and "isProjector a" and "isProjector b"
  shows "isProjector (R a o\<^sub>C\<^sub>L S b)"
  using assms unfolding isProjector_algebraic compatible_def
  apply auto
  apply (metis comp_update_assoc lvalue_mult)
  by (simp add: assms(2) assms(3) isProjector_D2 lvalue_projector)

(* TODO: write using "sandwich" *)
lemma assoc_ell2_sandwich: \<open>assoc a = assoc_ell2 o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L assoc_ell2'\<close>
  apply (rule tensor_extensionality3'[THEN fun_cong, where x=a])
  apply (simp add: assoc_hom)
   apply (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: assoc_apply times_applyOp tensor_op_ell2 assoc_ell2_tensor assoc_ell2'_tensor flip: tensor_ell2_ket)

end

