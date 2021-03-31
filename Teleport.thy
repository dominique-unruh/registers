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
abbreviation "X\<Phi>2 \<equiv> pair X \<Phi>2"
abbreviation "X\<Phi>1 \<equiv> pair X \<Phi>1"
abbreviation "X\<Phi> \<equiv> pair X \<Phi>"
abbreviation "XAB \<equiv> pair (pair X A) B"
abbreviation "AB \<equiv> pair A B"
abbreviation "\<Phi>2AB \<equiv> pair (pair (\<Phi> o Snd) A) B"

definition "teleport a b = [
    apply CNOT X\<Phi>1,
    apply hadamard X,
    ifthen \<Phi>1 a,
    ifthen X b, 
    apply (if a=1 then pauliX else idOp) \<Phi>2,
    apply (if b=1 then pauliZ else idOp) \<Phi>2
  ]"

definition "teleport_pre \<psi> = XAB =\<^sub>q \<psi> \<sqinter> \<Phi> =\<^sub>q \<beta>00"
definition "teleport_post \<psi> = \<Phi>2AB =\<^sub>q \<psi>"

lemma ell2_eq_vec_of_onb_enumI: 
  fixes a b :: "_::onb_enum"
  assumes "vec_of_onb_enum a = vec_of_onb_enum b"
  shows "a = b"
  by (metis assms onb_enum_of_vec_inverse)

lemma Uswap_apply[simp]: \<open>Uswap *\<^sub>V s \<otimes>\<^sub>s t = t \<otimes>\<^sub>s s\<close>
  apply (rule cbounded_linear_equal_ket[where f=\<open>\<lambda>s. Uswap *\<^sub>V s \<otimes>\<^sub>s t\<close>, THEN fun_cong])
  apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
  apply (simp add: clinear_tensor_ell21)
  apply (rule cbounded_linear_equal_ket[where f=\<open>\<lambda>t. Uswap *\<^sub>V _ \<otimes>\<^sub>s t\<close>, THEN fun_cong])
  apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
  apply (simp add: clinear_tensor_ell22)
  apply (rule ell2_eq_vec_of_onb_enumI)
  apply (simp add: mat_of_cblinfun_description vec_of_onb_enum_ket
      canonical_basis_length_ell2_def)
  by (case_tac i; case_tac ia; hypsubst_thin; normalization)

definition "sandwich a b = a o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L (a*)"
lemma clinear_sandwich[simp]: \<open>clinear (sandwich a)\<close>
  apply (rule clinearI)
  apply (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 sandwich_def)
  by (simp add: sandwich_def)

lemma sandwich_tensor: "sandwich (a \<otimes> b) = sandwich a \<otimes>\<^sub>h sandwich b"
  apply (rule tensor_extensionality)
  by (auto simp: sandwich_def tensor_update_hom_hom tensor_update_mult tensor_op_adjoint)

lemma sandwich_id: "sandwich idOp = idOp"
  by (metis eq_id_iff idOp.rep_eq idOp_adjoint sandwich_def times_idOp1 times_idOp2)

lemma apply_idOp[simp]: \<open>(*\<^sub>V) idOp = id\<close>
  by auto

lemma sandwich_grow_left: "sandwich a \<otimes>\<^sub>h id = sandwich (a \<otimes> idOp)"
  by (simp add: sandwich_tensor sandwich_id)

lemma lvalue_sandwich: \<open>lvalue F \<Longrightarrow> F (sandwich a b) = sandwich (F a) (F b)\<close>
  by (smt (verit, del_insts) lvalue_def sandwich_def)

lemma swap_sandwich: "swap = sandwich Uswap"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_def)
  apply (rule tensor_ell2_extensionality)
  by (simp add: times_applyOp tensor_op_ell2)

lemma enum_inj:
  assumes "i < CARD('a)" and "j < CARD('a)"
  shows "(Enum.enum ! i :: 'a::enum) = Enum.enum ! j \<longleftrightarrow> i = j"
  using inj_on_nth[OF enum_distinct, where I=\<open>{..<CARD('a)}\<close>]
  using assms by (auto dest: inj_onD simp flip: card_UNIV_length_enum)


lemma mat_of_cblinfun_assoc_ell2'[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2' :: (('a::enum\<times>('b::enum\<times>'c::enum)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  (is "mat_of_cblinfun ?assoc = _")
proof  (rule mat_eq_iff[THEN iffD2], intro conjI allI impI)

  show \<open>dim_row (mat_of_cblinfun ?assoc) =
    dim_row (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
    by (simp add: canonical_basis_length_ell2_def)
  show \<open>dim_col (mat_of_cblinfun ?assoc) =
    dim_col (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
    by (simp add: canonical_basis_length_ell2_def)

  fix i j
  let ?i = "Enum.enum ! i :: (('a\<times>'b)\<times>'c)" and ?j = "Enum.enum ! j :: ('a\<times>('b\<times>'c))"

  assume \<open>i < dim_row (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
  then have iB[simp]: \<open>i < CARD('a) * CARD('b) * CARD('c)\<close> by simp
  then have iB'[simp]: \<open>i < CARD('a) * (CARD('b) * CARD('c))\<close> by linarith
  assume \<open>j < dim_col (1\<^sub>m (CARD('a) * CARD('b) * CARD('c)))\<close>
  then have jB[simp]: \<open>j < CARD('a) * CARD('b) * CARD('c)\<close> by simp
  then have jB'[simp]: \<open>j < CARD('a) * (CARD('b) * CARD('c))\<close> by linarith

  define i1 i23 i2 i3
    where "i1 = fst (tensor_unpack CARD('a) (CARD('b)*CARD('c)) i)"
      and "i23 = snd (tensor_unpack CARD('a) (CARD('b)*CARD('c)) i)"
      and "i2 = fst (tensor_unpack CARD('b) CARD('c) i23)"
      and "i3 = snd (tensor_unpack CARD('b) CARD('c) i23)"
  define j12 j1 j2 j3
    where "j12 = fst (tensor_unpack (CARD('a)*CARD('b)) CARD('c) j)"
      and "j1 = fst (tensor_unpack CARD('a) CARD('b) j12)"
      and "j2 = snd (tensor_unpack CARD('a) CARD('b) j12)"
      and "j3 = snd (tensor_unpack (CARD('a)*CARD('b)) CARD('c) j)"

  have [simp]: "j12 < CARD('a)*CARD('b)" "i23 < CARD('b)*CARD('c)"
    using j12_def jB tensor_unpack_bound1 apply presburger
    using i23_def iB' tensor_unpack_bound2 by blast

  have j1': \<open>fst (tensor_unpack CARD('a) (CARD('b) * CARD('c)) j) = j1\<close>
    by (simp add: j1_def j12_def tensor_unpack_fstfst)

  let ?i1 = "Enum.enum ! i1 :: 'a" and ?i2 = "Enum.enum ! i2 :: 'b" and ?i3 = "Enum.enum ! i3 :: 'c"
  let ?j1 = "Enum.enum ! j1 :: 'a" and ?j2 = "Enum.enum ! j2 :: 'b" and ?j3 = "Enum.enum ! j3 :: 'c"

  have i: \<open>?i = ((?i1,?i2),?i3)\<close>
    by (auto simp add: enum_prod_nth_tensor_unpack case_prod_beta
          tensor_unpack_fstfst tensor_unpack_fstsnd tensor_unpack_sndsnd i1_def i2_def i23_def i3_def)
  have j: \<open>?j = (?j1,(?j2,?j3))\<close> 
    by (auto simp add: enum_prod_nth_tensor_unpack case_prod_beta
        tensor_unpack_fstfst tensor_unpack_fstsnd tensor_unpack_sndsnd j1_def j2_def j12_def j3_def)
  have ijeq: \<open>(?i1,?i2,?i3) = (?j1,?j2,?j3) \<longleftrightarrow> i = j\<close>
    unfolding i1_def i2_def i3_def j1_def j2_def j3_def apply simp
    apply (subst enum_inj, simp, simp)
    apply (subst enum_inj, simp, simp)
    apply (subst enum_inj, simp, simp)
    apply (subst tensor_unpack_inj[symmetric, where i=i and j=j and A="CARD('a)" and B="CARD('b)*CARD('c)"], simp, simp)
    unfolding prod_eq_iff
    apply (subst tensor_unpack_inj[symmetric, where i=\<open>snd (tensor_unpack CARD('a) (CARD('b) * CARD('c)) i)\<close> and A="CARD('b)" and B="CARD('c)"], simp, simp)
    by (simp add: i1_def[symmetric] j1_def[symmetric] i2_def[symmetric] j2_def[symmetric] i3_def[symmetric] j3_def[symmetric]
        i23_def[symmetric] j12_def[symmetric] j1'
        prod_eq_iff tensor_unpack_fstsnd tensor_unpack_sndsnd)

  have \<open>mat_of_cblinfun ?assoc $$ (i, j) = Rep_ell2 (assoc_ell2' *\<^sub>V ket ?j) ?i\<close>
    by (subst mat_of_cblinfun_ell2_index, auto)
  also have \<open>\<dots> = Rep_ell2 ((ket ?j1 \<otimes>\<^sub>s ket ?j2) \<otimes>\<^sub>s ket ?j3) ?i\<close>
    by (simp add: j assoc_ell2'_tensor flip: tensor_ell2_ket)
  also have \<open>\<dots> = (if (?i1,?i2,?i3) = (?j1,?j2,?j3) then 1 else 0)\<close>
    by (auto simp add: ket.rep_eq i)
  also have \<open>\<dots> = (if i=j then 1 else 0)\<close>
    using ijeq by simp
  finally
  show \<open>mat_of_cblinfun ?assoc $$ (i, j) =
           1\<^sub>m (CARD('a) * CARD('b) * CARD('c)) $$ (i, j)\<close>
    by auto
qed

lemma assoc_ell2'_inv: "assoc_ell2 o\<^sub>C\<^sub>L assoc_ell2' = idOp"
  apply (rule equal_ket, case_tac x, hypsubst)
  by (simp flip: tensor_ell2_ket add: times_applyOp assoc_ell2'_tensor assoc_ell2_tensor)

lemma assoc_ell2_inv: "assoc_ell2' o\<^sub>C\<^sub>L assoc_ell2 = idOp"
  apply (rule equal_ket, case_tac x, case_tac a, hypsubst)
  by (simp flip: tensor_ell2_ket add: times_applyOp assoc_ell2'_tensor assoc_ell2_tensor)

lemma mat_of_cblinfun_assoc_ell2[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2 :: ((('a::enum\<times>'b::enum)\<times>'c::enum) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  (is "mat_of_cblinfun ?assoc = _")
proof -
  let ?assoc' = "assoc_ell2' :: (('a::enum\<times>('b::enum\<times>'c::enum)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
  have "one_mat (CARD('a)*CARD('b)*CARD('c)) = mat_of_cblinfun (?assoc o\<^sub>C\<^sub>L ?assoc')"
    by (simp add: mult.assoc assoc_ell2'_inv cblinfun_of_mat_id canonical_basis_length_ell2_def)
  also have \<open>\<dots> = mat_of_cblinfun ?assoc * mat_of_cblinfun ?assoc'\<close>
    using cblinfun_of_mat_timesOp by blast
  also have \<open>\<dots> = mat_of_cblinfun ?assoc * one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
    by simp
  also have \<open>\<dots> = mat_of_cblinfun ?assoc\<close>
    apply (rule right_mult_one_mat')
    by (simp add: canonical_basis_length_ell2_def)
  finally show ?thesis
    by simp
qed


lemma [simp]: "dim_col (mat_adjoint m) = dim_row m"
  unfolding mat_adjoint_def by simp
lemma [simp]: "dim_row (mat_adjoint m) = dim_col m"
  unfolding mat_adjoint_def by simp

term tensor_update_hom
lemma
 tensor_update_hom_sandwich2: 
  fixes a :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2" and b :: "'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a::finite ell2"
  shows "id \<otimes>\<^sub>h (\<lambda>x. b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L a)
             = (\<lambda>x. (tensor_op idOp b) o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L (tensor_op idOp a))"
proof -
  have [simp]: \<open>clinear (id \<otimes>\<^sub>h (\<lambda>x. b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L a))\<close>
    by (auto intro!:  clinearI tensor_update_hom_hom simp add: cblinfun_apply_dist1 cblinfun_apply_dist2)
  have [simp]: \<open>clinear (\<lambda>x. tensor_op idOp b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L tensor_op idOp a)\<close>
    by (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)
  have [simp]: \<open>clinear (\<lambda>x. b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L a)\<close>
    by (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)
  show ?thesis
    apply (rule tensor_extensionality, simp, simp)
    apply (subst tensor_update_hom_apply, simp, simp)
    by (simp add: comp_tensor_op)
qed

lemma clinear_Fst[simp]: "clinear Fst"
  unfolding Fst_def by auto
lemma clinear_Snd[simp]: "clinear Snd"
  unfolding Fst_def by auto

lemma [compatible]: "mutually compatible (Fst, Snd)"
  using [[simproc del: compatibility_warn]]
  by (auto intro!: compatibleI simp add: Fst_def Snd_def comp_tensor_op)

(* TODO: Laws + rename *)
lemma pair_Fst_Snd[simp]: 
  assumes \<open>lvalue F\<close>
  shows \<open>pair (F o Fst) (F o Snd) = F\<close>
  apply (rule tensor_extensionality)
  using [[simproc del: compatibility_warn]]
  using assms by (auto simp: pair_apply Fst_def Snd_def lvalue_mult comp_tensor_op)

(* TODO: get rid of "Simplification subgoal compatible (F \<circ> Fst) F" warning *)

lemma \<Phi>_X\<Phi>: \<open>\<Phi> a = X\<Phi> (idOp \<otimes> a)\<close>
  by (auto simp: pair_apply)
lemma X\<Phi>1_X\<Phi>: \<open>X\<Phi>1 a = X\<Phi> (assoc (a \<otimes> idOp))\<close>
  apply (subst pair_comp_assoc[unfolded o_def, of X \<Phi>1 \<Phi>2, simplified, THEN fun_cong])
  by (auto simp: pair_apply)
lemma X\<Phi>2_X\<Phi>: \<open>X\<Phi>2 a = X\<Phi> ((id \<otimes>\<^sub>h swap) (assoc (a \<otimes> idOp)))\<close>
  apply (subst pair_comp_tensor[unfolded o_def, THEN fun_cong], simp, simp, simp)
  apply (subst (2) pair_Fst_Snd[symmetric, of \<Phi>], simp)
  using [[simproc del: compatibility_warn]]
  apply (subst pair_comp_swap', simp)
  apply (subst pair_comp_assoc[unfolded o_def, THEN fun_cong], simp, simp, simp)
  by (auto simp: pair_apply)
lemma \<Phi>2_X\<Phi>: \<open>\<Phi>2 a = X\<Phi> (idOp \<otimes> (idOp \<otimes> a))\<close>
  by (auto simp: Snd_def pair_apply)
lemmas to_X\<Phi> = \<Phi>_X\<Phi> X\<Phi>1_X\<Phi> X\<Phi>2_X\<Phi> \<Phi>2_X\<Phi>

lemma X_X\<Phi>1: \<open>X a = X\<Phi>1 (a \<otimes> idOp)\<close>
  by (auto simp: pair_apply)
lemmas to_X\<Phi>1 = X_X\<Phi>1

(* lemma clinear_comp_NO_MATCH:
  assumes "NO_MATCH (\<lambda>a. a) f"
  assumes "NO_MATCH (\<lambda>a. a) g"
  assumes "clinear f"
  assumes "clinear g"
  shows "clinear (\<lambda>x. f (g x))"
  by (simp add: assms(3) assms(4) clinearI complex_vector.linear_add complex_vector.linear_scale) *)

lemma X\<Phi>1_X\<Phi>1_AB: \<open>X\<Phi>1 a = (X\<Phi>1;AB) (a \<otimes> idOp)\<close>
  by (auto simp: pair_apply)
lemma XAB_X\<Phi>1_AB: \<open>XAB a = (X\<Phi>1;AB) (((\<lambda>x. x \<otimes> idOp) \<otimes>\<^sub>h id) (assoc a))\<close>
  by (simp add: pair_comp_tensor[unfolded o_def, THEN fun_cong] pair_apply
      pair_comp_assoc[unfolded o_def, THEN fun_cong])

lemmas to_X\<Phi>1_AB = X\<Phi>1_X\<Phi>1_AB XAB_X\<Phi>1_AB

lemma XAB_to_X\<Phi>2_AB: \<open>XAB a = (X\<Phi>2;AB) ((swap \<otimes>\<^sub>h id) (assoc' (idOp \<otimes> assoc a)))\<close>
  by (simp add: pair_comp_tensor[unfolded o_def, THEN fun_cong] pair_apply
      pair_comp_swap[unfolded o_def, THEN fun_cong]
      pair_comp_assoc'[unfolded o_def, THEN fun_cong]
      pair_comp_assoc[unfolded o_def, THEN fun_cong])

lemma X\<Phi>2_to_X\<Phi>2_AB: \<open>X\<Phi>2 a = (X\<Phi>2;AB) (a \<otimes> idOp)\<close>
  by (simp add: pair_apply)

schematic_goal \<Phi>2AB_to_X\<Phi>2_AB: "\<Phi>2AB a = (X\<Phi>2;AB) ?b"
  apply (subst pair_comp_assoc'[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  apply (subst pair_apply[where a=idOp])
    apply simp_all[2]
  apply (subst pair_comp_assoc[unfolded o_def, THEN fun_cong])
     apply simp_all[3]
  by simp

lemmas to_X\<Phi>2_AB = XAB_to_X\<Phi>2_AB X\<Phi>2_to_X\<Phi>2_AB \<Phi>2AB_to_X\<Phi>2_AB

(* TODO remove (use some generic transformation lemma instead) *)
lemma swap_lvalues_applySpace:
  assumes "compatible R S"
  shows "R a *\<^sub>S S b *\<^sub>S M = S b *\<^sub>S R a *\<^sub>S M"
  by (metis assms assoc_left(2) swap_lvalues)

lemma teleport:
  assumes [simp]: "norm \<psi> = 1"
  shows "hoare (teleport_pre \<psi>) (teleport a b) (teleport_post \<psi>)"
proof -
  define XZ :: \<open>bit update\<close> where "XZ = (if a=1 then (if b=1 then pauliZ o\<^sub>C\<^sub>L pauliX else pauliX) else (if b=1 then pauliZ else idOp))"

  define pre where "pre = EQ XAB \<psi>"

  define O1 where "O1 = EQP \<Phi> \<beta>00"
  have \<open>teleport_pre \<psi> = O1 *\<^sub>S pre\<close>
    unfolding pre_def O1_def teleport_pre_def EQ_def
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
  define O4 where \<open>O4 = EQP \<Phi>1 (ket a) o\<^sub>C\<^sub>L O3\<close>
  have \<open>hoare (O3 *\<^sub>S pre) [ifthen \<Phi>1 a] (O4 *\<^sub>S pre)\<close>
    apply (rule hoare_ifthen) by (simp add: O4_def assoc_left(2))

  also
  define O5 where \<open>O5 = EQP X (ket b) o\<^sub>C\<^sub>L O4\<close>
  have O5: \<open>O5 = X\<Phi>1 (butterfly (ket b \<otimes>\<^sub>s ket a) (CNOT *\<^sub>V (hadamard *\<^sub>V ket b) \<otimes>\<^sub>s ket a)) \<circ>\<^sub>d O1\<close> (is "_ = ?rhs")
  proof -
    have "O5 = EQP X\<Phi>1 (ket (b,a)) o\<^sub>C\<^sub>L O3"
      unfolding O5_def O4_def
      apply (subst join_EQP', simp)
      by simp
    also have \<open>\<dots> = ?rhs\<close>
      unfolding O3_def O2_def
      using [[simp_trace_new]]
      by (simp add: butterfly_times_right to_X\<Phi>1 times_applyOp tensor_op_adjoint tensor_op_ell2 flip: tensor_ell2_ket)
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
    by (auto simp add: O6_def O7_def XZ_def lvalue_mult)
  have \<open>hoare (O6 *\<^sub>S pre) [apply (if b=1 then pauliZ else idOp) (\<Phi> \<circ> Snd)] (O7 *\<^sub>S pre)\<close>
    apply (rule hoare_apply) 
    by (auto simp add: O7_def assoc_left(2))

  finally have hoare: \<open>hoare (teleport_pre \<psi>) (teleport a b) (O7 *\<^sub>S pre)\<close>
    by (auto simp add: teleport_def comp_def)

  have O5': "O5 = (1/2) *\<^sub>C \<Phi>2 (XZ*) o\<^sub>C\<^sub>L X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)"
    unfolding O7 O5 O1_def XZ_def
    apply (simp split del: if_split only: to_X\<Phi> lvalue_mult[of X\<Phi>])
    apply (simp split del: if_split add: lvalue_mult[of X\<Phi>] 
                flip: complex_vector.linear_scale
                del: comp_apply)
    apply (rule arg_cong[of _ _ X\<Phi>])
    apply (rule cblinfun_eq_mat_of_cblinfunI)
    apply (simp add: assoc_ell2_sandwich sandwich_def[abs_def] mat_of_cblinfun_tensor_op butterfly_def' cblinfun_of_mat_timesOp mat_of_cblinfun_ell2_to_l2bounded canonical_basis_length_ell2_def mat_of_cblinfun_adjoint' vec_of_onb_enum_ket cblinfun_of_mat_id swap_sandwich[abs_def]  mat_of_cblinfun_scaleR mat_of_cblinfun_scalarMult tensor_update_hom_sandwich2 vec_of_onb_enum_tensor_state mat_of_cblinfun_description)
    by normalization

  have [simp]: "unitary XZ"
    unfolding unitary_def unfolding XZ_def apply auto
    apply (metis assoc_left(1) pauliXX pauliZZ times_idOp2)
    by (metis assoc_left(1) pauliXX pauliZZ times_idOp2)

  have O7': "O7 = (1/2) *\<^sub>C X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket a \<otimes>\<^sub>s ket b) \<beta>00)"
    unfolding O7 O5'
    by (simp add: cblinfun_apply_assoc[symmetric] lvalue_mult[of \<Phi>2] del: comp_apply)

  have "O7 *\<^sub>S pre = X\<Phi>2 Uswap *\<^sub>S EQP XAB \<psi> *\<^sub>S \<Phi> (butterfly (ket (a, b)) \<beta>00) *\<^sub>S \<top>"
    apply (simp add: O7' pre_def EQ_def cblinfun_apply_assoc_subspace)
    apply (subst swap_lvalues_applySpace[where R=\<Phi> and S=XAB], simp)
    by simp
  also have \<open>\<dots> \<le> X\<Phi>2 Uswap *\<^sub>S EQP XAB \<psi> *\<^sub>S \<top>\<close>
    by (simp add: applyOpSpace_mono)
  also have \<open>\<dots> = (X\<Phi>2;AB) (Uswap \<otimes> id_update) *\<^sub>S (X\<Phi>2;AB) ((swap \<otimes>\<^sub>h id) (assoc' (id_update \<otimes> assoc (selfbutter \<psi>)))) *\<^sub>S \<top>\<close>
    by (simp add: to_X\<Phi>2_AB)
  also have \<open>\<dots> = EQP \<Phi>2AB \<psi> *\<^sub>S X\<Phi>2 Uswap *\<^sub>S \<top>\<close>
    apply (simp add: swap_sandwich sandwich_grow_left to_X\<Phi>2_AB   
        cblinfun_apply_assoc_subspace[symmetric]
        lvalue_mult)
    by (simp add: sandwich_def cblinfun_apply_assoc[symmetric] tensor_update_mult tensor_op_adjoint)
  also have \<open>\<dots> \<le> EQ \<Phi>2AB \<psi>\<close>
    by (simp add: EQ_def applyOpSpace_mono)
  finally have \<open>O7 *\<^sub>S pre \<le> teleport_post \<psi>\<close>
    by (simp add: teleport_post_def)

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

definition A :: "a_state var" where \<open>A a = a \<otimes> idOp \<otimes> idOp \<otimes> idOp \<otimes> idOp\<close>
definition X :: \<open>bit var\<close> where \<open>X a = idOp \<otimes> a \<otimes> idOp \<otimes> idOp \<otimes> idOp\<close>
definition \<Phi>1 :: \<open>bit var\<close> where \<open>\<Phi>1 a = idOp \<otimes> idOp \<otimes> a \<otimes> idOp \<otimes> idOp\<close>
definition B :: \<open>b_state var\<close> where \<open>B a = idOp \<otimes> idOp \<otimes> idOp \<otimes> a \<otimes> idOp\<close>
definition \<Phi>2 :: \<open>bit var\<close> where \<open>\<Phi>2 a = idOp \<otimes> idOp \<otimes> idOp \<otimes> idOp \<otimes> a\<close>
end


interpretation teleport_concrete:
  concrete_teleport_vars +
  teleport_locale concrete_teleport_vars.X
                  \<open>pair concrete_teleport_vars.\<Phi>1 concrete_teleport_vars.\<Phi>2\<close>
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
