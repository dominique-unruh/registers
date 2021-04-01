theory Quantum2
  imports Laws_Quantum "HOL-ex.Bit_Lists" "HOL-Library.Z2"
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

(* lemma pair_o_tensor':
  assumes "compatible A B" and \<open>clinear C\<close> and \<open>clinear D\<close>
  shows "(A; B) ((C \<otimes>\<^sub>h D) x) = (A o C; B o D) x"
  using pair_o_tensor[OF assms]
  by (smt (z3) fcomp_comp fcomp_def) *)

(* lemma pair_o_swap':
  assumes "compatible A B"
  shows "(A; B) (swap x) = (B; A) x"
  using pair_o_swap[OF assms]
  by (metis comp_def) *)

(* lemma id_update_tensor_lvalue[simp]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a. idOp \<otimes>\<^sub>o F a)\<close>
  using assms unfolding lvalue_def 
  apply auto
  using update_hom_tensor_left_is_hom[of idOp] linear_compose[of F \<open>\<lambda>x. idOp \<otimes>\<^sub>o x\<close>, unfolded o_def] o_def
  apply (smt (z3))
  apply (metis (no_types, hide_lams) comp_tensor_op times_idOp2)
  by (metis (full_types) idOp_adjoint tensor_op_adjoint) *)

(* lemma lvalue_tensor_id_update[simp]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a. F a \<otimes>\<^sub>o idOp)\<close>
  using assms unfolding lvalue_def 
  apply auto
  using update_hom_tensor_right_is_hom[of idOp] linear_compose[of F \<open>\<lambda>x. x \<otimes>\<^sub>o idOp\<close>, unfolded o_def] o_def
  apply (smt (z3))
  apply (metis (no_types, hide_lams) comp_tensor_op times_idOp2)
  by (metis (full_types) idOp_adjoint tensor_op_adjoint) *)

lemma lvalue_id[simp]: \<open>lvalue (\<lambda>x. x)\<close>
  by (metis (mono_tags, lifting) complex_vector.module_hom_ident lvalue_def)

(* lemma compatible_tensor_id_update_left[simp]:
  assumes "compatible F G"
  shows "compatible (\<lambda>a. idOp \<otimes>\<^sub>o F a) (\<lambda>a. idOp \<otimes>\<^sub>o G a)"
  using assms unfolding compatible_def apply auto
  by (metis comp_tensor_op) *)

(* lemma compatible_tensor_id_update_left1[simp]:
  assumes "lvalue F" and "lvalue G"
  shows "compatible (\<lambda>a. F a \<otimes>\<^sub>o idOp) (\<lambda>a. idOp \<otimes>\<^sub>o G a)"
  using assms unfolding compatible_def apply auto
  by (metis (no_types, hide_lams) comp_tensor_op times_idOp1 times_idOp2) *)

(* lemma compatible_tensor_id_update_left2[simp]:
  assumes "lvalue F" and "lvalue G"
  shows "compatible (\<lambda>a. idOp \<otimes>\<^sub>o F a) (\<lambda>a. G a \<otimes>\<^sub>o idOp)"
  using assms unfolding compatible_def apply auto
  by (metis (no_types, hide_lams) comp_tensor_op times_idOp1 times_idOp2) *)

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
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  using assms unfolding isProjector_algebraic compatible_def
  apply auto
  apply (metis comp_update_assoc lvalue_mult)
  by (simp add: assms(2) assms(3) isProjector_D2 lvalue_projector)

lemma sandwich_tensor: "sandwich (a \<otimes>\<^sub>o b) = sandwich a \<otimes>\<^sub>h sandwich b"
  for a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
  apply (rule tensor_extensionality)
  by (auto simp: sandwich_def tensor_update_hom_is_hom tensor_update_mult tensor_op_adjoint)

lemma sandwich_grow_left: "sandwich a \<otimes>\<^sub>h id = sandwich (a \<otimes>\<^sub>o idOp)"
  for a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
    by (simp add: sandwich_tensor sandwich_id)

lemma lvalue_sandwich: \<open>lvalue F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) lvalue_def sandwich_def)

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

end

