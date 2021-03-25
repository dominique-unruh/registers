theory Quantum2
  imports Laws_Quantum "HOL-ex.Bit_Lists" "HOL-Library.Z2"
    Bounded_Operators.Bounded_Operators_Matrices
begin

no_notation meet (infixl "\<sqinter>\<index>" 70)
unbundle lvalue_notation

lemma lvalue_id[simp]: \<open>lvalue id\<close>
  unfolding lvalue_def by auto

(* declare lvalue_hom[simp] *)

lemma pair_comp_tensor':
  assumes "compatible A B" and \<open>lvalue C\<close> and \<open>lvalue D\<close>
  shows "(pair A B) ((C \<otimes>\<^sub>h D) x) = (pair (A o C) (B o D)) x"
  using pair_comp_tensor[OF assms]
  by (smt (z3) fcomp_comp fcomp_def)

lemma pair_comp_swap:
  assumes "compatible A B"
  shows "(pair A B) o swap = pair B A"
  apply (rule tensor_extensionality)
  apply (meson Complex_Vector_Spaces.linear_compose assms lvalue_hom pair_lvalue swap_hom)
  apply (simp add: assms compatible_sym lvalue_hom)
  by (metis (no_types, lifting) swap_apply assms comp_def compatible_def lvalue_hom pair_apply)

lemma pair_comp_swap':
  assumes "compatible A B"
  shows "(pair A B) (swap x) = pair B A x"
  using pair_comp_swap[OF assms]
  by (metis comp_def)


lemma tensor_butterfly[simp]: "butterfly \<psi> \<otimes> butterfly \<phi> = butterfly (\<psi> \<otimes>\<^sub>s \<phi>)"
  sorry

(* TODO Laws *)
lemma swap_lvalues:
  assumes "compatible R S"
  shows "R A o\<^sub>C\<^sub>L S B = S B o\<^sub>C\<^sub>L R A"
  using assms compatible_def by blast

(* TODO Laws *)
lemma join_lvalues:
  assumes "compatible R S"
  shows "R A o\<^sub>C\<^sub>L S B = (pair R S) (A \<otimes> B)"
  by (metis assms compatible_def lvalue_hom pair_apply)

definition Fst where \<open>Fst a = tensor_maps a idOp\<close>
definition Snd where \<open>Snd a = tensor_maps idOp a\<close>

lemma lvalue_Fst[simp]: \<open>lvalue Fst\<close>
  by (auto simp: Fst_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

lemma lvalue_Snd[simp]: \<open>lvalue Snd\<close>
  by (auto simp: Snd_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

lemma clinear_Fst[simp]: \<open>clinear Fst\<close>
  by (auto simp: Fst_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

lemma clinear_Snd[simp]: \<open>clinear Snd\<close>
  by (auto simp: Snd_def[abs_def] lvalue_def comp_tensor_op tensor_op_adjoint)

(* TODO in Laws *)
lemma lvalue_of_id[simp]: \<open>lvalue R \<Longrightarrow> R idOp = idOp\<close>
  by (auto simp: lvalue_def)

(* TODO Laws *)
lemma lvalue_comp'1[simp]: \<open>lvalue R \<Longrightarrow> R A o\<^sub>C\<^sub>L (R B o\<^sub>C\<^sub>L C) = R (A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
  by (metis (no_types, lifting) assoc_left(1) lvalue_mult)


instantiation bit :: enum begin
definition "enum_bit = [0::bit,1]"
definition "enum_all_bit P \<longleftrightarrow> P (0::bit) \<and> P 1"
definition "enum_ex_bit P \<longleftrightarrow> P (0::bit) \<or> P 1"
instance
  apply intro_classes
  apply (auto simp: enum_bit_def enum_all_bit_def enum_ex_bit_def)
  by (metis bit_not_one_imp)+
end

locale teleport_locale =
  fixes X :: "(bit,'mem::finite) maps_hom"
    and \<Phi> :: "(bit*bit,'mem::finite) maps_hom"
    and A :: "('atype::finite,'mem) maps_hom"
    and B :: "('btype::finite,'mem) maps_hom"
  assumes compat[compatible]: "mutually compatible (X,\<Phi>,A,B)"
begin

definition "apply U R = R U" for R :: \<open>('a,'mem) maps_hom\<close>
definition "ifthen R x = R (butter x x)" for R :: \<open>('a,'mem) maps_hom\<close>
definition "program S = fold (o\<^sub>C\<^sub>L) S idOp" for S :: \<open>'mem domain_end list\<close>

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

definition "teleport a b = [
    apply CNOT (pair X (\<Phi> \<circ> Fst)),
    apply hadamard X,
    ifthen (\<Phi> \<circ> Fst) a,
    ifthen X b, 
    apply (if a=1 then pauliX else idOp) (\<Phi> \<circ> Snd),
    apply (if b=1 then pauliZ else idOp) (\<Phi> \<circ> Snd)
  ]"

definition hoare :: \<open>'mem ell2 clinear_space \<Rightarrow> ('mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2) list \<Rightarrow> 'mem ell2 clinear_space \<Rightarrow> bool\<close> where
  "hoare C p D \<longleftrightarrow> (\<forall>\<psi>\<in>space_as_set C. program p *\<^sub>V \<psi> \<in> space_as_set D)" for C p D

definition "EQP R \<psi> = R (butterfly \<psi>)" for R :: \<open>('a,'mem) maps_hom\<close>
definition "EQ R \<psi> = EQP R \<psi> *\<^sub>S \<top>" for R :: \<open>('a,'mem) maps_hom\<close>

lemma swap_EQP:
  assumes "compatible R S"
  shows "EQP R \<psi> o\<^sub>C\<^sub>L EQP S \<phi> = EQP S \<phi> o\<^sub>C\<^sub>L EQP R \<psi>"
  unfolding EQP_def
  by (rule swap_lvalues[OF assms])

lemma swap_EQP':
  assumes "compatible R S"
  shows "EQP R \<psi> o\<^sub>C\<^sub>L (EQP S \<phi> o\<^sub>C\<^sub>L C) = EQP S \<phi> o\<^sub>C\<^sub>L (EQP R \<psi> o\<^sub>C\<^sub>L C)"
  by (simp add: assms assoc_left(1) swap_EQP)

lemma join_EQP:
  assumes "compatible R S"
  shows "EQP R \<psi> o\<^sub>C\<^sub>L EQP S \<phi> = EQP (pair R S) (\<psi> \<otimes>\<^sub>s \<phi>)"
  unfolding EQP_def
  apply (subst join_lvalues[OF assms])
  by simp

lemma join_EQP':
  assumes "compatible R S"
  shows "EQP R \<psi> o\<^sub>C\<^sub>L (EQP S \<phi> o\<^sub>C\<^sub>L C) = EQP (pair R S) (\<psi> \<otimes>\<^sub>s \<phi>) o\<^sub>C\<^sub>L C"
  by (simp add: assms assoc_left(1) join_EQP)


definition "teleport_pre \<psi> = EQ (pair (pair X A) B) \<psi> \<sqinter> EQ \<Phi> \<beta>00"
definition "teleport_post \<psi> = EQ (pair (pair (\<Phi> o Snd) A) B) \<psi>"

lemma program_seq: "program (p1@p2) = program p2 o\<^sub>C\<^sub>L program p1"
  apply (induction p1)
  unfolding program_def
   apply auto
  sorry


lemma hoare_seq[trans]: "hoare C p1 D \<Longrightarrow> hoare D p2 E \<Longrightarrow> hoare C (p1@p2) E"
  by (auto simp: program_seq hoare_def times_applyOp)

lemma hoare_skip: "C \<le> D \<Longrightarrow> hoare C [] D"
  by (auto simp: program_def hoare_def times_applyOp in_mono less_eq_clinear_space.rep_eq)

lemma hoare_apply: 
  assumes "R U *\<^sub>S pre \<le> post"
  shows "hoare pre [apply U R] post"
  using assms 
  apply (auto simp: hoare_def program_def apply_def)
  by (metis (no_types, lifting) applyOpSpace.rep_eq closure_subset imageI less_eq_clinear_space.rep_eq subsetD)

lemma hoare_ifthen: 
  fixes R :: \<open>('a,'mem) maps_hom\<close>
  assumes "EQP R (ket x) *\<^sub>S pre \<le> post"
  shows "hoare pre [ifthen R x] post"
  using assms 
  apply (auto simp: hoare_def program_def ifthen_def EQP_def butter_def)
  by (metis (no_types, lifting) applyOpSpace.rep_eq butterfly_def closure_subset imageI less_eq_clinear_space.rep_eq subsetD)

lemma "hoare (teleport_pre \<psi>) (teleport a b) (teleport_post \<psi>)" for \<psi> a b
proof -
  define XZ :: \<open>bit domain_end\<close> where "XZ = (if a=1 then (if b=1 then pauliZ o\<^sub>C\<^sub>L pauliX else pauliX) else (if b=1 then pauliZ else idOp))"

  define pre post where "pre = teleport_pre \<psi>" and "post = teleport_post \<psi>"
  define O1 where "O1 = EQP \<Phi> \<beta>00"
  have \<open>hoare pre [] (O1 *\<^sub>S pre)\<close>
    apply (rule hoare_skip) unfolding pre_def O1_def
    sorry

  also
  define O2 where "O2 = ((pair X (\<Phi> \<circ> Fst)) CNOT) o\<^sub>C\<^sub>L O1"
  have \<open>hoare (O1 *\<^sub>S pre) [apply CNOT (pair X (\<Phi> \<circ> Fst))] (O2 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O2_def assoc_left(2))

  also
  define O3 where \<open>O3 = X hadamard o\<^sub>C\<^sub>L O2\<close>
  have \<open>hoare (O2 *\<^sub>S pre) [apply hadamard X] (O3 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O3_def assoc_left(2))

  also
  define O4 where \<open>O4 = EQP (\<Phi> \<circ> Fst) (ket a) o\<^sub>C\<^sub>L O3\<close>
  have \<open>hoare (O3 *\<^sub>S pre) [ifthen (\<Phi> \<circ> Fst) a] (O4 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O4_def assoc_left(2))

  also
  define O5 where \<open>O5 = EQP X (ket b) o\<^sub>C\<^sub>L O4\<close>
  have O5_def': "O5 = EQP (pair (\<Phi>\<circ>Fst) X) (ket (a,b)) o\<^sub>C\<^sub>L O3"
    unfolding O5_def O4_def
    apply (subst swap_EQP')
     apply (rule compatible_comp_right, simp, simp) (* TODO: automate *)
    apply (subst join_EQP')
     apply (rule compatible_comp_left, simp, simp) (* TODO: automate *)
    by simp
  have \<open>hoare (O4 *\<^sub>S pre) [ifthen X b] (O5 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O5_def assoc_left(2))

  also
  define O6 where \<open>O6 = (\<Phi> \<circ> Snd) (if a=1 then pauliX else idOp) o\<^sub>C\<^sub>L O5\<close>
  have \<open>hoare (O5 *\<^sub>S pre) [apply (if a=1 then pauliX else idOp) (\<Phi> \<circ> Snd)] (O6 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (auto simp add: O6_def assoc_left(2))

  also
  define O7 where \<open>O7 = (\<Phi> \<circ> Snd) XZ o\<^sub>C\<^sub>L O5\<close>
  have \<open>hoare (O6 *\<^sub>S pre) [apply (if b=1 then pauliZ else idOp) (\<Phi> \<circ> Snd)] (O7 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) 
    by (auto simp add: O6_def O7_def assoc_left(2) XZ_def lvalue_mult)

  finally have \<open>hoare pre (teleport a b) (O7 *\<^sub>S pre)\<close>
    by (auto simp add: teleport_def)

  have join1: "\<Phi> M = (pair X \<Phi>) (idOp \<otimes> M)" for M
    by (metis (no_types, lifting) compat compatible_lvalue2 join_lvalues lvalue_def times_idOp2)
  have join2: \<open>(pair (\<Phi> \<circ> Fst) X) M = (pair X \<Phi>) ((id \<otimes>\<^sub>h Fst) (swap M))\<close> for M
    apply (subst pair_comp_tensor')
       apply simp_all[3]
    apply (subst pair_comp_swap', simp)
    by simp
  have join3: "X M = (pair X \<Phi>) (M \<otimes> idOp)" for M
    by (metis (no_types, lifting) compat compatible_def join_lvalues lvalue_of_id times_idOp1)
  have join4: \<open>(pair X (\<Phi> \<circ> Fst)) M = (pair X \<Phi>) ((id \<otimes>\<^sub>h Fst) M)\<close> for M
    apply (subst pair_comp_tensor')
    by simp_all

  have "O7 = xxx"
    unfolding O7_def O5_def' O3_def O2_def O1_def
    apply (simp only: join1 join2 join3 join4 EQP_def)
    apply simp
    unfolding join1x

    apply (simp add: join1)x
    by -
  show ?thesis
    by -
qed



end

end
