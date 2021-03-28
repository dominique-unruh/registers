theory Quantum2
  imports Laws_Quantum "HOL-ex.Bit_Lists" "HOL-Library.Z2"
    Bounded_Operators.Bounded_Operators_Matrices
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

definition Fst where \<open>Fst a = tensor_maps a idOp\<close>
definition Snd where \<open>Snd a = tensor_maps idOp a\<close>

lemma lvalue_Fst[simp]: \<open>lvalue Fst\<close>
  by (auto simp: Fst_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

lemma lvalue_Snd[simp]: \<open>lvalue Snd\<close>
  by (auto simp: Snd_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

lemma lvalue_of_id[simp]: \<open>lvalue R \<Longrightarrow> R idOp = idOp\<close>
  by (auto simp: lvalue_def)

lemma lvalue_comp'1[simp]: \<open>lvalue R \<Longrightarrow> R A o\<^sub>C\<^sub>L (R B o\<^sub>C\<^sub>L C) = R (A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
  by (metis (no_types, lifting) assoc_left(1) lvalue_mult)


definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
definition CNOT :: \<open>(bit*bit) domain_end\<close> where "CNOT = cblinfun_of_mat matrix_CNOT"

lemma [simp]: "mat_of_cblinfun CNOT = matrix_CNOT"
  apply (auto simp add: CNOT_def matrix_CNOT_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto simp add: canonical_basis_length_ell2_def)

definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
definition hadamard :: \<open>bit domain_end\<close> where "hadamard = cblinfun_of_mat matrix_hadamard"

lemma [simp]: "mat_of_cblinfun hadamard = matrix_hadamard"
  apply (auto simp add: hadamard_def matrix_hadamard_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto simp add: canonical_basis_length_ell2_def)

definition "matrix_pauliX = mat_of_rows_list 2 [ [0::complex, 1], [1, 0] ]"
definition pauliX :: \<open>bit domain_end\<close> where "pauliX = cblinfun_of_mat matrix_pauliX"
lemma [simp]: "mat_of_cblinfun pauliX = matrix_pauliX"
  apply (auto simp add: pauliX_def matrix_pauliX_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto simp add: canonical_basis_length_ell2_def)

definition "matrix_pauliZ = mat_of_rows_list 2 [ [1::complex, 0], [0, -1] ]"
definition pauliZ :: \<open>bit domain_end\<close> where "pauliZ = cblinfun_of_mat matrix_pauliZ"
lemma [simp]: "mat_of_cblinfun pauliZ = matrix_pauliZ"
  apply (auto simp add: pauliZ_def matrix_pauliZ_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto simp add: canonical_basis_length_ell2_def)

definition "vector_\<beta>00 = vec_of_list [ 1/sqrt 2::complex, 0, 0, 1/sqrt 2 ]"
definition \<beta>00 :: \<open>(bit\<times>bit) ell2\<close> where "\<beta>00 = onb_enum_of_vec vector_\<beta>00"
lemma [simp]: "vec_of_onb_enum \<beta>00 = vector_\<beta>00"
  apply (auto simp add: \<beta>00_def vector_\<beta>00_def)
  apply (subst onb_enum_of_vec_inverse')
  by (auto simp add: canonical_basis_length_ell2_def)

definition "vector_ketplus = vec_of_list [ 1/sqrt 2::complex, 1/sqrt 2 ]"
definition ketplus :: \<open>bit ell2\<close> ("|+\<rangle>") where \<open>ketplus = onb_enum_of_vec vector_ketplus\<close>
lemma [simp]: "vec_of_onb_enum ketplus = vector_ketplus"
  apply (auto simp add: ketplus_def vector_ketplus_def)
  apply (subst onb_enum_of_vec_inverse')
  by (auto simp add: canonical_basis_length_ell2_def)

definition "matrix_Uswap = mat_of_rows_list 4 [ [1::complex, 0, 0, 0], [0,0,1,0], [0,1,0,0], [0,0,0,1] ]"
definition Uswap :: \<open>(bit\<times>bit) domain_end\<close> where \<open>Uswap = cblinfun_of_mat matrix_Uswap\<close>

lemma [simp]: "mat_of_cblinfun Uswap = matrix_Uswap"
  apply (auto simp add: Uswap_def matrix_Uswap_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto simp add: canonical_basis_length_ell2_def)

lemma [simp]: "dim_col matrix_Uswap = 4"
  unfolding matrix_Uswap_def by simp
lemma [simp]: "dim_row matrix_Uswap = 4"
  unfolding matrix_Uswap_def by simp

(* lemma compatible_compatible0:
  assumes \<open>lvalue F\<close> and \<open>lvalue G\<close>
  assumes \<open>compatible0 F G\<close>
  shows \<open>compatible F G\<close>
  using assms unfolding compatible0_def compatible_def by simp *)

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
  apply (metis comp_domain_assoc lvalue_mult)
  by (simp add: assms(2) assms(3) isProjector_D2 lvalue_projector)

end

