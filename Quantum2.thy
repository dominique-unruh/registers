theory Quantum2
  imports Laws_Quantum "HOL-ex.Bit_Lists" "HOL-Library.Z2"
    Bounded_Operators.Bounded_Operators_Matrices
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
unbundle lvalue_notation

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

(* (* TODO Laws *)
lemma join_lvalues:
  assumes "compatible R S"
  shows "R A o\<^sub>C\<^sub>L S B = (pair R S) (A \<otimes> B)"
  apply (subst pair_apply)
  apply auto
  by (metis assms compatible_def lvalue_hom pair_apply) *)

definition Fst where \<open>Fst a = tensor_maps a idOp\<close>
definition Snd where \<open>Snd a = tensor_maps idOp a\<close>

lemma lvalue_Fst[simp]: \<open>lvalue Fst\<close>
  by (auto simp: Fst_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

lemma lvalue_Snd[simp]: \<open>lvalue Snd\<close>
  by (auto simp: Snd_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

(* TODO in Laws *)
lemma lvalue_of_id[simp]: \<open>lvalue R \<Longrightarrow> R idOp = idOp\<close>
  by (auto simp: lvalue_def)

(* TODO Laws *)
lemma lvalue_comp'1[simp]: \<open>lvalue R \<Longrightarrow> R A o\<^sub>C\<^sub>L (R B o\<^sub>C\<^sub>L C) = R (A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
  by (metis (no_types, lifting) assoc_left(1) lvalue_mult)


definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
definition CNOT :: \<open>(bit*bit) domain_end\<close> where "CNOT = cblinfun_of_mat matrix_CNOT"
definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
definition hadamard :: \<open>bit domain_end\<close> where "hadamard = cblinfun_of_mat matrix_hadamard"
definition "matrix_pauliX = mat_of_rows_list 2 [ [0::complex, 1], [1, 0] ]"
definition pauliX :: \<open>bit domain_end\<close> where "pauliX = cblinfun_of_mat matrix_pauliX"
definition "matrix_pauliZ = mat_of_rows_list 2 [ [1::complex, 0], [0, -1] ]"
definition pauliZ :: \<open>bit domain_end\<close> where "pauliZ = cblinfun_of_mat matrix_pauliZ"
definition "vector_\<beta>00 = vec_of_list [ 1/sqrt 2::complex, 0, 0, 1/sqrt 2 ]"
definition \<beta>00 :: \<open>(bit*bit) ell2\<close> where "\<beta>00 = onb_enum_of_vec vector_\<beta>00"



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


end

