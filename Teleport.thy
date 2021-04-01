theory Teleport
  imports QHoare
    Real_Impl.Real_Impl "HOL-Library.Code_Target_Numeral"
    Finite_Tensor_Product_Matrices
begin

hide_const (open) Finite_Cartesian_Product.vec
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.row
hide_const (open) Finite_Cartesian_Product.column
no_notation Group.mult (infixl "\<otimes>\<index>" 70)
no_notation Order.top ("\<top>\<index>")
unbundle no_vec_syntax
unbundle no_inner_syntax




locale teleport_locale = qhoare "TYPE('mem::finite)" +
  fixes X :: "(bit,'mem::finite) update_hom"
    and \<Phi> :: "(bit*bit,'mem) update_hom"
    and A :: "('atype::finite,'mem) update_hom"
    and B :: "('btype::finite,'mem) update_hom"
  assumes compat[compatible]: "mutually compatible (X,\<Phi>,A,B)"
begin

abbreviation "\<Phi>1 \<equiv> \<Phi> \<circ> Fst"
abbreviation "\<Phi>2 \<equiv> \<Phi> \<circ> Snd"
abbreviation "X\<Phi>2 \<equiv> (X;\<Phi>2)"
abbreviation "X\<Phi>1 \<equiv> (X;\<Phi>1)"
abbreviation "X\<Phi> \<equiv> (X;\<Phi>)"
abbreviation "XAB \<equiv> ((X;A); B)"
abbreviation "AB \<equiv> (A;B)"
abbreviation "\<Phi>2AB \<equiv> ((\<Phi> o Snd; A); B)"

definition "teleport a b = [
    apply CNOT X\<Phi>1,
    apply hadamard X,
    ifthen \<Phi>1 a,
    ifthen X b, 
    apply (if a=1 then pauliX else idOp) \<Phi>2,
    apply (if b=1 then pauliZ else idOp) \<Phi>2
  ]"

(* definition "teleport_pre \<psi> = XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00" *)
(* definition "teleport_post \<psi> = \<Phi>2AB =\<^sub>q \<psi>" *)

(* lemma clinear_Fst[simp]: "clinear Fst"
  unfolding Fst_def by auto *)
(* lemma clinear_Snd[simp]: "clinear Snd"
  apply simp
  unfolding Fst_def by auto *)

(* lemma [compatible]: "mutually compatible (Fst, Snd)"
  using [[simproc del: compatibility_warn]]
  by (auto intro!: compatibleI simp add: Fst_def Snd_def comp_tensor_op) *)

(* lemma pair_Fst_Snd[simp]: 
  assumes \<open>lvalue F\<close>
  shows \<open>(F o Fst; F o Snd) = F\<close>
  apply (rule tensor_extensionality)
  using [[simproc del: compatibility_warn]]
  using assms by (auto simp: lvalue_pair_apply Fst_def Snd_def lvalue_mult comp_tensor_op) *)

lemma \<Phi>_X\<Phi>: \<open>\<Phi> a = X\<Phi> (idOp \<otimes>\<^sub>o a)\<close>
  by (auto simp: lvalue_pair_apply)
lemma X\<Phi>1_X\<Phi>: \<open>X\<Phi>1 a = X\<Phi> (assoc (a \<otimes>\<^sub>o idOp))\<close>
  apply (subst pair_o_assoc[unfolded o_def, of X \<Phi>1 \<Phi>2, simplified, THEN fun_cong])
  by (auto simp: lvalue_pair_apply)
lemma X\<Phi>2_X\<Phi>: \<open>X\<Phi>2 a = X\<Phi> ((id \<otimes>\<^sub>h swap) (assoc (a \<otimes>\<^sub>o idOp)))\<close>
  apply (subst pair_o_tensor[unfolded o_def, THEN fun_cong], simp, simp, simp)
  apply (subst (2) lvalue_Fst_lvalue_Snd[symmetric, of \<Phi>], simp)
  using [[simproc del: compatibility_warn]]
  apply (subst pair_o_swap[unfolded o_def], simp)
  apply (subst pair_o_assoc[unfolded o_def, THEN fun_cong], simp, simp, simp)
  by (auto simp: lvalue_pair_apply)
lemma \<Phi>2_X\<Phi>: \<open>\<Phi>2 a = X\<Phi> (idOp \<otimes>\<^sub>o (idOp \<otimes>\<^sub>o a))\<close>
  by (auto simp: Snd_def lvalue_pair_apply)
lemmas to_X\<Phi> = \<Phi>_X\<Phi> X\<Phi>1_X\<Phi> X\<Phi>2_X\<Phi> \<Phi>2_X\<Phi>

lemma X_X\<Phi>1: \<open>X a = X\<Phi>1 (a \<otimes>\<^sub>o idOp)\<close>
  by (auto simp: lvalue_pair_apply)
lemmas to_X\<Phi>1 = X_X\<Phi>1

(* lemma clinear_comp_NO_MATCH:
  assumes "NO_MATCH (\<lambda>a. a) f"
  assumes "NO_MATCH (\<lambda>a. a) g"
  assumes "clinear f"
  assumes "clinear g"
  shows "clinear (\<lambda>x. f (g x))"
  by (simp add: assms(3) assms(4) clinearI complex_vector.linear_add complex_vector.linear_scale) *)

lemma X\<Phi>1_X\<Phi>1_AB: \<open>X\<Phi>1 a = (X\<Phi>1;AB) (a \<otimes>\<^sub>o idOp)\<close>
  by (auto simp: lvalue_pair_apply)
lemma XAB_X\<Phi>1_AB: \<open>XAB a = (X\<Phi>1;AB) (((\<lambda>x. x \<otimes>\<^sub>o idOp) \<otimes>\<^sub>h id) (assoc a))\<close>
  by (simp add: pair_o_tensor[unfolded o_def, THEN fun_cong] lvalue_pair_apply
      pair_o_assoc[unfolded o_def, THEN fun_cong])

lemmas to_X\<Phi>1_AB = X\<Phi>1_X\<Phi>1_AB XAB_X\<Phi>1_AB

lemma XAB_to_X\<Phi>2_AB: \<open>XAB a = (X\<Phi>2;AB) ((swap \<otimes>\<^sub>h id) (assoc' (idOp \<otimes>\<^sub>o assoc a)))\<close>
  by (simp add: pair_o_tensor[unfolded o_def, THEN fun_cong] lvalue_pair_apply
      pair_o_swap[unfolded o_def, THEN fun_cong]
      pair_o_assoc'[unfolded o_def, THEN fun_cong]
      pair_o_assoc[unfolded o_def, THEN fun_cong])

lemma X\<Phi>2_to_X\<Phi>2_AB: \<open>X\<Phi>2 a = (X\<Phi>2;AB) (a \<otimes>\<^sub>o idOp)\<close>
  by (simp add: lvalue_pair_apply)

schematic_goal \<Phi>2AB_to_X\<Phi>2_AB: "\<Phi>2AB a = (X\<Phi>2;AB) ?b"
  apply (subst pair_o_assoc'[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  apply (subst lvalue_pair_apply[where a=idOp])
    apply simp_all[2]
  apply (subst pair_o_assoc[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  by simp

lemmas to_X\<Phi>2_AB = XAB_to_X\<Phi>2_AB X\<Phi>2_to_X\<Phi>2_AB \<Phi>2AB_to_X\<Phi>2_AB

(* lemma swap_lvalues_applySpace:
  assumes "compatible R S"
  shows "R a *\<^sub>S S b *\<^sub>S M = S b *\<^sub>S R a *\<^sub>S M"
  by (metis assms assoc_left(2) swap_lvalues) *)

lemma teleport:
  assumes [simp]: "norm \<psi> = 1"
  shows "hoare (XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) (teleport a b) (\<Phi>2AB =\<^sub>q \<psi>)"
proof -
  define XZ :: \<open>bit update\<close> where "XZ = (if a=1 then (if b=1 then pauliZ o\<^sub>C\<^sub>L pauliX else pauliX) else (if b=1 then pauliZ else idOp))"

  define pre where "pre = XAB =\<^sub>q \<psi>"

  define O1 where "O1 = \<Phi> (selfbutter \<beta>00)"
  have \<open>(XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) = O1 *\<^sub>S pre\<close>
    unfolding pre_def O1_def EQ_def
    apply (subst compatible_proj_intersect[where R=XAB and S=\<Phi>])
       apply (simp_all add: butterfly_isProjector)
    apply (subst swap_lvalues[where R=XAB and S=\<Phi>])
    by (simp_all add: assoc_left(2))

  also
  define O2 where "O2 = X\<Phi>1 CNOT o\<^sub>C\<^sub>L O1"
  have \<open>hoare (O1 *\<^sub>S pre) [apply CNOT X\<Phi>1] (O2 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O2_def assoc_left(2))

  also
  define O3 where \<open>O3 = X hadamard o\<^sub>C\<^sub>L O2\<close>
  have \<open>hoare (O2 *\<^sub>S pre) [apply hadamard X] (O3 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (simp add: O3_def assoc_left(2))

  also
  define O4 where \<open>O4 = \<Phi>1 (selfbutterket a) o\<^sub>C\<^sub>L O3\<close>
  have \<open>hoare (O3 *\<^sub>S pre) [ifthen \<Phi>1 a] (O4 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O4_def assoc_left(2))

  also
  define O5 where \<open>O5 = X (selfbutterket b) o\<^sub>C\<^sub>L O4\<close>
  have O5: \<open>O5 = X\<Phi>1 (butterfly (ket b \<otimes>\<^sub>s ket a) (CNOT *\<^sub>V (hadamard *\<^sub>V ket b) \<otimes>\<^sub>s ket a)) o\<^sub>C\<^sub>L O1\<close> (is "_ = ?rhs")
  proof -
    have "O5 = X\<Phi>1 (selfbutterket (b,a)) o\<^sub>C\<^sub>L O3"
      unfolding O5_def O4_def
      apply (subst lift_cblinfun_comp[OF join_EQP, where R1=X and S1=\<Phi>1], simp)
      by simp
    also have \<open>\<dots> = ?rhs\<close>
      unfolding O3_def O2_def
      by (simp add: butterfly_times_right to_X\<Phi>1 times_applyOp tensor_op_adjoint tensor_op_ell2 
                    lift_cblinfun_comp[OF lvalue_mult] flip: tensor_ell2_ket)
    finally show ?thesis by -
  qed
  have \<open>hoare (O4 *\<^sub>S pre) [ifthen X b] (O5 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O5_def assoc_left(2))

  also
  define O6 where \<open>O6 = \<Phi>2 (if a=1 then pauliX else idOp) o\<^sub>C\<^sub>L O5\<close>
  have \<open>hoare (O5 *\<^sub>S pre) [apply (if a=1 then pauliX else idOp) (\<Phi> \<circ> Snd)] (O6 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) by (auto simp add: O6_def assoc_left(2))

  also
  define O7 where \<open>O7 = \<Phi>2 (if b = 1 then pauliZ else idOp) o\<^sub>C\<^sub>L O6\<close>
  have O7: \<open>O7 = \<Phi>2 XZ o\<^sub>C\<^sub>L O5\<close>
    by (auto simp add: O6_def O7_def XZ_def lvalue_mult lift_cblinfun_comp[OF lvalue_mult])
  have \<open>hoare (O6 *\<^sub>S pre) [apply (if b=1 then pauliZ else idOp) (\<Phi> \<circ> Snd)] (O7 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) 
    by (auto simp add: O7_def assoc_left(2))

  finally have hoare: \<open>hoare (XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00) (teleport a b) (O7 *\<^sub>S pre)\<close>
    by (auto simp add: teleport_def comp_def)

  have O5': "O5 = (1/2) *\<^sub>C \<Phi>2 (XZ*) o\<^sub>C\<^sub>L X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)"
    unfolding O7 O5 O1_def XZ_def
    apply (simp split del: if_split only: to_X\<Phi> lvalue_mult[of X\<Phi>])
    apply (simp split del: if_split add: lvalue_mult[of X\<Phi>] 
                flip: complex_vector.linear_scale
                del: comp_apply)
    apply (rule arg_cong[of _ _ X\<Phi>])
    apply (rule cblinfun_eq_mat_of_cblinfunI)
    apply (simp add: assoc_ell2_sandwich mat_of_cblinfun_tensor_op
                     butterfly_def' cblinfun_of_mat_timesOp mat_of_cblinfun_ell2_to_l2bounded 
                     canonical_basis_length_ell2_def mat_of_cblinfun_adjoint' vec_of_onb_enum_ket 
                     cblinfun_of_mat_id swap_sandwich[abs_def] mat_of_cblinfun_scaleR mat_of_cblinfun_scalarMult
                     id_tensor_sandwich vec_of_onb_enum_tensor_state mat_of_cblinfun_description
                     mat_of_cblinfun_sandwich)
    by normalization

  have [simp]: "unitary XZ"
    unfolding unitary_def unfolding XZ_def apply auto
    apply (metis assoc_left(1) pauliXX pauliZZ times_idOp2)
    by (metis assoc_left(1) pauliXX pauliZZ times_idOp2)

  have O7': "O7 = (1/2) *\<^sub>C X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)"
    unfolding O7 O5'
    by (simp add: cblinfun_apply_assoc[symmetric] lvalue_mult[of \<Phi>2] del: comp_apply)

  have "O7 *\<^sub>S pre = X\<Phi>2 Uswap *\<^sub>S XAB (selfbutter \<psi>) *\<^sub>S \<Phi> (butterfly (ket (a, b)) \<beta>00) *\<^sub>S \<top>"
    apply (simp add: O7' pre_def EQ_def cblinfun_apply_assoc_subspace)
    apply (subst lift_cblinfun_comp[OF swap_lvalues[where R=\<Phi> and S=XAB]], simp)
    by (simp add: assoc_left(2))
  also have \<open>\<dots> \<le> X\<Phi>2 Uswap *\<^sub>S XAB (selfbutter \<psi>) *\<^sub>S \<top>\<close>
    by (simp add: applyOpSpace_mono)
  also have \<open>\<dots> = (X\<Phi>2;AB) (Uswap \<otimes>\<^sub>o id_update) *\<^sub>S (X\<Phi>2;AB) ((swap \<otimes>\<^sub>h id) (assoc' (id_update \<otimes>\<^sub>o assoc (selfbutter \<psi>)))) *\<^sub>S \<top>\<close>
    by (simp add: to_X\<Phi>2_AB)
  also have \<open>\<dots> = \<Phi>2AB (selfbutter \<psi>) *\<^sub>S X\<Phi>2 Uswap *\<^sub>S \<top>\<close>
    apply (simp add: swap_sandwich sandwich_grow_left to_X\<Phi>2_AB   
        cblinfun_apply_assoc_subspace[symmetric]
        lvalue_mult)
    by (simp add: sandwich_def cblinfun_apply_assoc[symmetric] tensor_update_mult tensor_op_adjoint)
  also have \<open>\<dots> \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
    by (simp add: EQ_def applyOpSpace_mono)
  finally have \<open>O7 *\<^sub>S pre \<le> \<Phi>2AB =\<^sub>q \<psi>\<close>
    by simp

  with hoare
  show ?thesis
    by (meson basic_trans_rules(31) hoare_def less_eq_clinear_space.rep_eq)
qed

end


locale concrete_teleport_vars begin

type_synonym a_state = "64 word"
type_synonym b_state = "1000000 word"
type_synonym mem = "a_state * bit * bit * b_state * bit"
type_synonym 'a var = \<open>('a,mem) update_hom\<close>

definition A :: "a_state var" where \<open>A a = a \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp\<close>
definition X :: \<open>bit var\<close> where \<open>X a = idOp \<otimes>\<^sub>o a \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp\<close>
definition \<Phi>1 :: \<open>bit var\<close> where \<open>\<Phi>1 a = idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o a \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp\<close>
definition B :: \<open>b_state var\<close> where \<open>B a = idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o a \<otimes>\<^sub>o idOp\<close>
definition \<Phi>2 :: \<open>bit var\<close> where \<open>\<Phi>2 a = idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o idOp \<otimes>\<^sub>o a\<close>
end


interpretation teleport_concrete:
  concrete_teleport_vars +
  teleport_locale concrete_teleport_vars.X
                  \<open>(concrete_teleport_vars.\<Phi>1; concrete_teleport_vars.\<Phi>2)\<close>
                  concrete_teleport_vars.A
                  concrete_teleport_vars.B
  apply standard
  using [[simproc del: compatibility_warn]]
  by (auto simp: concrete_teleport_vars.X_def[abs_def]
                 concrete_teleport_vars.\<Phi>1_def[abs_def]
                 concrete_teleport_vars.\<Phi>2_def[abs_def]
                 concrete_teleport_vars.A_def[abs_def]
                 concrete_teleport_vars.B_def[abs_def]
           intro!: compatible3' compatible3)

thm teleport
thm teleport_def


end
