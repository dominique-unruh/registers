theory Quantum
  imports Jordan_Normal_Form.Matrix_Impl "HOL-Library.Rewrite"
          Bounded_Operators.Complex_L2
begin


unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)

definition bra :: "'a \<Rightarrow> (_,complex) cblinfun" where "bra i = vector_to_cblinfun (ket i)*" for i

instantiation mat :: (conjugate) conjugate
begin

definition conjugate_mat :: "'a :: conjugate mat \<Rightarrow> 'a mat"
  where "conjugate M = map_mat conjugate M"

instance
proof intro_classes
  fix M N :: \<open>'a mat\<close>
  show \<open>conjugate (conjugate M) = M\<close>
    unfolding conjugate_mat_def by auto
  show \<open>(conjugate M = conjugate N) = (M = N)\<close>
    unfolding conjugate_mat_def by (auto simp: mat_eq_iff)
qed
end

lemma conjugate_carrier_mat[simp]: \<open>M \<in> carrier_mat n m \<Longrightarrow> conjugate M \<in> carrier_mat n m\<close>
  unfolding conjugate_mat_def by auto

lemma dim_row_conjugate[simp]: \<open>dim_row (conjugate M) = dim_row M\<close>
  unfolding conjugate_mat_def by auto

lemma dim_col_conjugate[simp]: \<open>dim_col (conjugate M) = dim_col M\<close>
  unfolding conjugate_mat_def by auto

lemma conjugate_index[simp]: \<open>i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> conjugate A $$ (i,j) = conjugate (A $$ (i,j))\<close>
  unfolding conjugate_mat_def by auto

(* lemma row_conjugate_mat[simp]: \<open>i < dim_row A \<Longrightarrow> row (conjugate A) i = conjugate (row A i)\<close>
  unfolding conjugate_mat_def by auto *)

lemma col_conjugate_mat[simp]: \<open>i < dim_col A \<Longrightarrow> col (conjugate A) i = conjugate (col A i)\<close>
  unfolding conjugate_mat_def by auto

lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto

(* lemma index_mat_fstsnd:  "fst x < nr \<Longrightarrow> snd x < nc \<Longrightarrow> mat nr nc f $$ x = f x"
  apply (cases x) by auto *)

definition tensor_pack :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat" where "tensor_pack X Y = (\<lambda>(x, y). x * Y + y)"
definition tensor_unpack :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"  where "tensor_unpack X Y xy = (xy div Y, xy mod Y)"

lemma tensor_unpack_bound1[simp]: "i < A * B \<Longrightarrow> fst (tensor_unpack A B i) < A"
  unfolding tensor_unpack_def
  apply auto
  using less_mult_imp_div_less by blast

lemma tensor_unpack_bound2[simp]: "i < A * B \<Longrightarrow> snd (tensor_unpack A B i) < B"
  unfolding tensor_unpack_def
  apply auto
  by (metis mod_less_divisor mult.commute mult_zero_left nat_neq_iff not_less0)

lemma tensor_unpack_pack[simp]: "j < B \<Longrightarrow> tensor_unpack A B (tensor_pack A B (i, j)) = (i,j)"
  unfolding tensor_unpack_def tensor_pack_def
  by auto

lemma tensor_pack_unpack[simp]: "x < A*B \<Longrightarrow> tensor_pack A B (tensor_unpack A B x) = x"
  unfolding tensor_unpack_def tensor_pack_def
  by auto

lemma tensor_pack_bound[simp]:
  "i < A \<Longrightarrow> j < B \<Longrightarrow> tensor_pack A B (i, j) < A * B"
  unfolding tensor_pack_def apply auto
  by (smt (verit, ccfv_SIG) Euclidean_Division.div_eq_0_iff div_mult2_eq div_mult_self3 le_add_same_cancel1 less_add_same_cancel1 mult.commute nat_neq_iff not_le)

lemma tensor_pack_inj[simp]: \<open>inj_on (tensor_pack A B) ({0..<A} \<times> {0..<B})\<close>
  apply (rule inj_onI)
  by (metis SigmaE atLeastLessThan_iff tensor_unpack_pack)

lemma tensor_pack_range[simp]: \<open>tensor_pack A B ` ({0..<A} \<times> {0..<B}) = {0..<A*B}\<close>
  apply auto unfolding image_iff Bex_def
  apply (rule_tac x=\<open>tensor_unpack A B x\<close> in exI)
  by (auto simp: mem_Times_iff)

lemma tensor_pack_sum[simp]: \<open>(\<Sum>ij = 0..<A*B. f ij) = 
    (\<Sum>i = 0..<A. \<Sum>j = 0..<B. f (tensor_pack A B (i,j)))\<close>
    apply (subst sum.cartesian_product) apply simp
    apply (subst sum.reindex[where h=\<open>tensor_pack A B\<close>, unfolded o_def, symmetric])
  by auto

lemma tensor_unpack_fstfst: \<open>fst (tensor_unpack A B (fst (tensor_unpack (A * B) C i)))
     = fst (tensor_unpack A (B * C) i)\<close>
  unfolding tensor_unpack_def apply auto
  by (metis div_mult2_eq mult.commute)
lemma tensor_unpack_sndsnd: \<open>snd (tensor_unpack B C (snd (tensor_unpack A (B * C) i)))
     = snd (tensor_unpack (A * B) C i)\<close>
  unfolding tensor_unpack_def apply auto
  by (meson dvd_triv_right mod_mod_cancel)
lemma tensor_unpack_fstsnd: \<open>fst (tensor_unpack B C (snd (tensor_unpack A (B * C) i)))
     = snd (tensor_unpack A B (fst (tensor_unpack (A * B) C i)))\<close>
  unfolding tensor_unpack_def apply auto
  by (metis (no_types, lifting) Euclidean_Division.div_eq_0_iff add_0_iff bits_mod_div_trivial div_mult_self4 mod_mult2_eq mod_mult_self1_is_0 mult.commute)

type_synonym 'a state = \<open>'a ell2\<close>
type_synonym 'a domain_end = \<open>('a state, 'a state) cblinfun\<close>

abbreviation comp_domain :: "'a domain_end \<Rightarrow> 'a domain_end \<Rightarrow> 'a domain_end" where
  "comp_domain \<equiv> timesOp"

lemma comp_domain_assoc: "comp_domain (comp_domain a b) c = comp_domain a (comp_domain b c)"
  by (simp add: cblinfun_apply_assoc)


type_synonym ('a,'b) maps_hom = \<open>'a domain_end \<Rightarrow> 'b domain_end\<close>
abbreviation (input) maps_hom :: \<open>('a,'b) maps_hom \<Rightarrow> bool\<close> where
  "maps_hom \<equiv> clinear"

lemma id_maps_hom: \<open>maps_hom id\<close>
  by (fact complex_vector.linear_id)

lemma comp_maps_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (G \<circ> F)"
  by (simp add: Complex_Vector_Spaces.linear_compose) 

type_synonym ('a,'b,'c) maps_2hom = \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> 'c domain_end\<close>
abbreviation (input) maps_2hom :: "('a, 'b, 'c) maps_2hom \<Rightarrow> bool" where
  "maps_2hom \<equiv> cbilinear"

(* lemma maps_2hom_bilinear: "maps_2hom F \<longleftrightarrow> cbilinear F"
  by (meson cbilinear_def maps_2hom_def maps_hom_def) *)

lemma maps_hom_2hom_comp: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. G (F2 a b))\<close>
  apply (auto simp: cbilinear_def intro!: clinearI)
  apply (smt (z3) clinear_additive_D)
  apply (metis complex_vector.linear_scale)
  apply (simp add: clinear_additive_D)
  by (simp add: complex_vector.linear_scale)
lemma maps_2hom_hom_comp1: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. F2 (G a) b)\<close>
  apply (auto simp: cbilinear_def intro!: clinearI)
  apply (smt (z3) clinear_additive_D)
  by (metis complex_vector.linear_scale)
lemma maps_2hom_sym: \<open>maps_2hom F2 \<Longrightarrow> maps_2hom (\<lambda>a b. F2 b a)\<close> 
  by (auto simp: cbilinear_def)
lemma maps_2hom_left: \<open>maps_2hom F2 \<Longrightarrow> maps_hom (\<lambda>a. F2 a b)\<close>
  by (auto simp: cbilinear_def)


lemma comp_2hom: "maps_2hom timesOp"
  by (auto intro!: clinearI simp add: cbilinear_def cblinfun_apply_dist1 cblinfun_apply_dist2)

lift_definition tensor_state :: \<open>'a::finite state \<Rightarrow> 'b::finite state \<Rightarrow> ('a\<times>'b) state\<close> (infixr "\<otimes>\<^sub>s" 70) is
  \<open>\<lambda>\<psi> \<phi> (i,j). \<psi> i * \<phi> j\<close>
  by simp

lemma tensor_state_add2: \<open>tensor_state a (b + c) = tensor_state a b + tensor_state a c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (meson ordered_field_class.sign_simps(42))

lemma tensor_state_add1: \<open>tensor_state (a + b) c = tensor_state a c + tensor_state b c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (simp add: vector_space_over_itself.scale_left_distrib)

lemma tensor_state_scaleC2: \<open>tensor_state a (c *\<^sub>C b) = c *\<^sub>C tensor_state a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_state_scaleC1: \<open>tensor_state (c *\<^sub>C a) b = c *\<^sub>C tensor_state a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_state_inner_prod[simp]: \<open>\<langle>tensor_state a b, tensor_state c d\<rangle> = \<langle>a,c\<rangle> * \<langle>b,d\<rangle>\<close>
  apply transfer
  by (auto simp: case_prod_beta sum_product sum.cartesian_product mult.assoc mult.left_commute)

lemma clinear_tensor_state1: "clinear (\<lambda>b. tensor_state a b)"
  apply (rule clinearI; transfer)
  apply (auto simp: case_prod_beta)
  by (simp add: cond_case_prod_eta ordered_field_class.sign_simps(42))

lemma clinear_tensor_state2: "clinear (\<lambda>a. tensor_state a b)"
  apply (rule clinearI; transfer)
  apply (auto simp: case_prod_beta)
  by (simp add: case_prod_beta' mult.commute ordered_field_class.sign_simps(42))

lemma tensor_state_ket[simp]: "tensor_state (ket i) (ket j) = ket (i,j)"
  apply transfer by auto

definition tensor_op :: \<open>('a ell2, 'b::finite ell2) cblinfun \<Rightarrow> ('c ell2, 'd::finite ell2) cblinfun
      \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) cblinfun\<close> where
  \<open>tensor_op M N = (SOME P. \<forall>a c. P *\<^sub>V (ket (a,c))
      = tensor_state (M *\<^sub>V ket a) (N *\<^sub>V ket c))\<close>

lemma tensor_op_ket: 
  fixes a :: \<open>'a::finite\<close> and b :: \<open>'b\<close> and c :: \<open>'c::finite\<close> and d :: \<open>'d\<close>
  shows \<open>tensor_op M N *\<^sub>V (ket (a,c)) = tensor_state (M *\<^sub>V ket a) (N *\<^sub>V ket c)\<close>
proof -
  define S :: \<open>('a\<times>'c) state set\<close> where "S = ket ` UNIV"
  define \<phi> where \<open>\<phi> = (\<lambda>(a,c). tensor_state (M *\<^sub>V ket a) (N *\<^sub>V ket c))\<close>
  define \<phi>' where \<open>\<phi>' = \<phi> \<circ> inv ket\<close>

  have def: \<open>tensor_op M N = (SOME P. \<forall>a c. P *\<^sub>V (ket (a,c)) = \<phi> (a,c))\<close>
    unfolding tensor_op_def \<phi>_def by auto

  have \<open>cindependent S\<close>
    using S_def cindependent_ket by blast
  moreover have \<open>cspan S = UNIV\<close>
    by (metis S_def finite_class.finite_UNIV finite_imageI ket_ell2_span span_finite_dim)
  moreover have \<open>finite S\<close>
    using S_def finite_class.finite_UNIV by blast
  ultimately have "cblinfun_extension_exists S \<phi>'"
    by (rule cblinfun_extension_exists_finite)
  then have "\<exists>P. \<forall>x\<in>S. P *\<^sub>V x = \<phi>' x"
    unfolding cblinfun_extension_exists_def by auto
  then have ex: \<open>\<exists>P. \<forall>a c. P *\<^sub>V ket (a,c) = \<phi> (a,c)\<close>
    by (metis S_def \<phi>'_def comp_eq_dest_lhs inj_ket inv_f_f rangeI)


  then have \<open>tensor_op M N *\<^sub>V (ket (a,c)) = \<phi> (a,c)\<close>
    unfolding def apply (rule someI2_ex[where P=\<open>\<lambda>P. \<forall>a c. P *\<^sub>V (ket (a,c)) = \<phi> (a,c)\<close>])
    by auto
  then show ?thesis
    unfolding \<phi>_def by auto
qed

(* TODO should be in bounded operators (non-finite case). Implicitly proven in: *)
thm equal_basis_0
thm equal_ket
thm superposition_principle_linear_ket
lemma cbounded_linear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>clinear f\<close>
  assumes \<open>clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule complex_vector.linear_eq_on_span[where f=f and g=g and B=\<open>range ket\<close>])
  using assms apply auto
  by (metis ket_ell2_span span_finite_dim finite_class.finite_UNIV finite_imageI iso_tuple_UNIV_I) 

lemma cbounded_linear_finite_ell2[simp, intro!]:
  fixes f :: \<open>'a::finite ell2 \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes "clinear f"
  shows \<open>cbounded_linear f\<close>
  apply (subst cblinfun_operator_finite_dim[where basis=\<open>ket ` UNIV\<close>])
  using assms apply (auto intro!: cindependent_ket)
  by (metis finite_class.finite_UNIV finite_imageI iso_tuple_UNIV_I ket_ell2_span span_finite_dim)

lemma tensor_op_state: "tensor_op A B *\<^sub>V tensor_state \<psi> \<phi> = tensor_state (A *\<^sub>V \<psi>) (B *\<^sub>V \<phi>)"
proof -
  have 1: \<open>clinear (\<lambda>a. tensor_op A B *\<^sub>V tensor_state a (ket b))\<close> for b
    by (auto intro!: clinearI simp: tensor_state_add1 tensor_state_scaleC1 cblinfun_apply_add)
  have 2: \<open>clinear (\<lambda>a. tensor_state (A *\<^sub>V a) (B *\<^sub>V ket b))\<close> for b
    by (auto intro!: clinearI simp: tensor_state_add1 tensor_state_scaleC1 cblinfun_apply_add)
  have 3: \<open>clinear (\<lambda>a. tensor_op A B *\<^sub>V tensor_state \<psi> a)\<close>
    by (auto intro!: clinearI simp: tensor_state_add2 tensor_state_scaleC2 cblinfun_apply_add)
  have 4: \<open>clinear (\<lambda>a. tensor_state (A *\<^sub>V \<psi>) (B *\<^sub>V a))\<close>
    by (auto intro!: clinearI simp: tensor_state_add2 tensor_state_scaleC2 cblinfun_apply_add)

  have eq_ket_ket: \<open>tensor_op A B *\<^sub>V tensor_state (ket a) (ket b) = tensor_state (A *\<^sub>V ket a) (B *\<^sub>V ket b)\<close> for a b
    by (simp add: tensor_op_ket)
  have eq_ket: \<open>tensor_op A B *\<^sub>V tensor_state \<psi> (ket b) = tensor_state (A *\<^sub>V \<psi>) (B *\<^sub>V ket b)\<close> for b
    apply (rule fun_cong[where x=\<psi>])
    using 1 2 eq_ket_ket by (rule cbounded_linear_equal_ket)
  show ?thesis 
    apply (rule fun_cong[where x=\<phi>])
    using 3 4 eq_ket by (rule cbounded_linear_equal_ket)
qed

lemma comp_tensor_op: "(tensor_op a b) o\<^sub>C\<^sub>L (tensor_op c d) = tensor_op (a o\<^sub>C\<^sub>L c) (b o\<^sub>C\<^sub>L d)"
  for a :: "'e::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2" and b :: "'f::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2" and
  c :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'e ell2" and d :: "'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'f ell2"
  apply (rule equal_ket)
  apply (rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
  by (simp flip: tensor_state_ket add: tensor_op_state times_applyOp)

(* lemma tensor_op_conjugate[simp]: "tensor_op (conjugate_op a) (conjugate_op b) = conjugate_op (tensor_op a b)"
  apply transfer
  by (auto simp: conjugate_mat_def mat_eq_iff case_prod_beta) *)

(* lemma tensor_op_transpose[simp]: "tensor_op (transpose_op a) (transpose_op b) = transpose_op (tensor_op a b)"
  apply transfer
  by (auto simp: mat_eq_iff case_prod_beta) *)

(* lemma tensor_op_adjoint[simp]: "tensor_op (adjoint_op a) (adjoint_op b) = adjoint_op (tensor_op a b)"
  unfolding adjoint_op_def by simp *)

lemma tensor_op_adjoint: \<open>(tensor_op a b)* = tensor_op (a*) (b*)\<close>
  apply (rule cinner_ket_adjointI[symmetric])
  apply (auto simp flip: tensor_state_ket simp: tensor_op_state)
  by (simp add: adjoint_I)

abbreviation tensor_maps :: \<open>'a::finite domain_end \<Rightarrow> 'b::finite domain_end \<Rightarrow> ('a\<times>'b) domain_end\<close> where
  \<open>tensor_maps \<equiv> tensor_op\<close>

(* TODO belongs into bounded operators *)
lemma apply_cblinfun_distr_left: "(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x"
  apply transfer by simp

lemma tensor_maps_cbilinear: \<open>cbilinear tensor_maps\<close>
proof -
  have \<open>clinear (\<lambda>b. tensor_maps a b)\<close> for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
    apply (rule clinearI)
     apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
     apply (simp flip: tensor_state_ket add: tensor_op_state apply_cblinfun_distr_left tensor_state_add2)
    apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
    by (simp flip: tensor_state_ket add: tensor_op_state apply_cblinfun_distr_left tensor_state_scaleC2)

  moreover have \<open>clinear (\<lambda>a. tensor_maps a b)\<close> for b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    apply (rule clinearI)
     apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
     apply (simp flip: tensor_state_ket add: tensor_op_state apply_cblinfun_distr_left tensor_state_add1)
    apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
    by (simp flip: tensor_state_ket add: tensor_op_state apply_cblinfun_distr_left tensor_state_scaleC1)

  ultimately show ?thesis
    unfolding cbilinear_def by auto
qed

lemma tensor_2hom: \<open>maps_2hom tensor_maps\<close>
  by (simp add: tensor_maps_cbilinear)

definition \<open>butter i j = vector_to_cblinfun (ket i) o\<^sub>C\<^sub>L (vector_to_cblinfun (ket j) :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*\<close>

lemma ket_Kronecker_delta: \<open>\<langle>ket i, ket j\<rangle> = (if i=j then 1 else 0)\<close>
  by (simp add: ket_Kronecker_delta_eq ket_Kronecker_delta_neq)

lemma sum_butter[simp]: \<open>(\<Sum>(i::'a::finite)\<in>UNIV. butter i i) = idOp\<close>
  apply (rule equal_ket)
  apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>y. y *\<^sub>V ket _\<close>])
  apply (auto simp add: apply_cblinfun_distr_left clinearI butter_def times_applyOp ket_Kronecker_delta)
  apply (subst sum.mono_neutral_cong_right[where S=\<open>{_}\<close>])
  by auto

lemma linfun_cspan: \<open>cspan {butter i j| (i::'b::finite) (j::'a::finite). True} = UNIV\<close>
proof (rule, simp, rule)
  fix f :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  have frep: \<open>f = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i))\<close>
  proof (rule cblinfun_ext)
    fix \<phi> :: \<open>'a ell2\<close>
    have \<open>f *\<^sub>V \<phi> = f *\<^sub>V (\<Sum>i\<in>UNIV. butter i i) *\<^sub>V \<phi>\<close>
      by auto
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      apply (subst (2) complex_vector.linear_sum)
       apply (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. butter j j) *\<^sub>V f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. butter j j *\<^sub>V f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      apply (subst (3) complex_vector.linear_sum)
       apply (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
      by simp
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. butter j j *\<^sub>V f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      by (simp add: sum.cartesian_product)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i *\<^sub>V \<phi>))\<close>
      by (simp add: butter_def times_applyOp mult.commute)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i)) *\<^sub>V \<phi>\<close>
      unfolding applyOp_scaleC1[symmetric] case_prod_beta
      thm complex_vector.linear_sum
      apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>x. x *\<^sub>V \<phi>\<close>])
       apply (simp add: apply_cblinfun_distr_left clinearI)
      by simp
    finally show \<open>f *\<^sub>V \<phi> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i)) *\<^sub>V \<phi>\<close>
      by -
  qed
  show \<open>f \<in> cspan {butter i j |i j. True}\<close>
    apply (subst frep)
    apply (auto simp: case_prod_beta)
    by (metis (mono_tags, lifting) complex_vector.span_base complex_vector.span_scale complex_vector.span_sum mem_Collect_eq)
qed

ML \<open>
\<^term>\<open>{f x y | x y. P x y}\<close>
\<close>


lemma linfun_cindependent: \<open>cindependent {butter i j| (i::'b::finite) (j::'a::finite). True}\<close>
proof (rule independent_if_scalars_zero)
  show finite: \<open>finite {butter (i::'b) (j::'a) |i j. True}\<close>
    apply (subst (6) conj.left_neutral[symmetric])
    apply (rule finite_image_set2)
    by auto
  fix f :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> complex\<close> and g :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  define lin where \<open>lin = (\<Sum>g\<in>{butter i j |i j. True}. f g *\<^sub>C g)\<close>
  assume \<open>lin = 0\<close>
  assume \<open>g \<in> {butter i j |i j. True}\<close>
  then obtain i j where g: \<open>g = butter i j\<close>
    by auto
  (* define bra :: "'b \<Rightarrow> (_,complex) cblinfun" where "bra i = vector_to_cblinfun (ket i)*" for i *)

  have *: "bra i *\<^sub>V f g *\<^sub>C g *\<^sub>V ket j = 0"
    if \<open>g\<in>{butter i j |i j. True} - {butter i j}\<close> for g 
  proof -
    from that
    obtain i' j' where g: \<open>g = butter i' j'\<close>
      by auto
    from that have \<open>g \<noteq> butter i j\<close> by auto
    with g consider (i) \<open>i\<noteq>i'\<close> | (j) \<open>j\<noteq>j'\<close>
      by auto
    then show \<open>bra i *\<^sub>V f g *\<^sub>C g *\<^sub>V ket j = 0\<close>
    proof cases
      case i
      then show ?thesis 
        unfolding g by (auto simp: butter_def times_applyOp bra_def ket_Kronecker_delta_neq)
    next
      case j
      then show ?thesis
        unfolding g by (auto simp: butter_def times_applyOp ket_Kronecker_delta_neq)
    qed
  qed

  have \<open>0 = bra i *\<^sub>V lin *\<^sub>V ket j\<close>
    using \<open>lin = 0\<close> by auto
  also have \<open>\<dots> = (\<Sum>g\<in>{butter i j |i j. True}. bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j)\<close>
    unfolding lin_def
    apply (rule complex_vector.linear_sum)
    by (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
  also have \<open>\<dots> = (\<Sum>g\<in>{butter i j}. bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j)\<close>
    apply (rule sum.mono_neutral_right)
    using finite * by auto
  also have \<open>\<dots> = bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j\<close>
    by (simp add: g)
  also have \<open>\<dots> = f g\<close>
    unfolding g 
    by (auto simp: butter_def times_applyOp bra_def ket_Kronecker_delta_eq)
  finally show \<open>f g = 0\<close>
    by simp
qed

lemma tensor_butter: \<open>tensor_op (butter i j) (butter k l) = butter (i,k) (j,l)\<close>
  for i :: "_" and j :: "_::finite" and k :: "_" and l :: "_::finite"
  apply (rule equal_ket, case_tac x)
  apply (auto simp flip: tensor_state_ket simp: times_applyOp tensor_op_state butter_def)
  by (auto simp: tensor_state_scaleC1 tensor_state_scaleC2)

lemma cspan_tensor_op: \<open>cspan {tensor_op (butter i j) (butter k l)| i (j::_::finite) k (l::_::finite). True} = UNIV\<close>
  unfolding tensor_butter
  apply (subst linfun_cspan[symmetric])
  by (metis surj_pair)

lemma cindependent_tensor_op: \<open>cindependent {tensor_op (butter i j) (butter k l)| i (j::_::finite) k (l::_::finite). True}\<close>
  unfolding tensor_butter
  using linfun_cindependent
  by (smt (z3) Collect_mono_iff complex_vector.independent_mono)


lemma tensor_extensionality:
  fixes F G :: \<open>('a::finite\<times>'b::finite, 'c) maps_hom\<close>
  assumes [simp]: "maps_hom F" "maps_hom G"
  assumes tensor_eq: "(\<And>a b. F (tensor_op a b) = G (tensor_op a b))"
  shows "F = G"
proof (rule ext, rule complex_vector.linear_eq_on_span[where f=F and g=G])
  show \<open>clinear F\<close> and \<open>clinear G\<close>
    using assms by (simp_all add: cbilinear_def)
  show \<open>x \<in> cspan  {tensor_op (butter i j) (butter k l)| i j k l. True}\<close> 
    for x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
    using cspan_tensor_op by auto
  show \<open>F x = G x\<close> if \<open>x \<in> {tensor_maps (butter i j) (butter k l) |i j k l. True}\<close> for x
    using that by (auto simp: tensor_eq)
qed

lemma tensor_id[simp]: \<open>tensor_maps idOp idOp = idOp\<close>
  apply (rule equal_ket, case_tac x)
  by (simp flip: tensor_state_ket add: tensor_op_state)

definition tensor_lift :: \<open>('a::finite, 'b::finite, 'c) maps_2hom \<Rightarrow> (('a\<times>'b, 'c) maps_hom)\<close> where
  "tensor_lift F2 = (SOME G. clinear G \<and> (\<forall>a b. G (tensor_maps a b) = F2 a b))"

lemma assumes "maps_2hom F2"
  shows tensor_lift_hom: "maps_hom (tensor_lift F2)"
  and tensor_existence:  \<open>(\<lambda>a b. tensor_lift F2 (tensor_maps a b)) = F2\<close>
proof -
  define F2' t4 \<phi> where
    \<open>F2' = tensor_lift F2\<close> and
    \<open>t4 = (\<lambda>(i,j,k,l). tensor_maps (butter i j) (butter k l))\<close> and
    \<open>\<phi> m = (let (i,j,k,l) = inv t4 m in F2 (butter i j) (butter k l))\<close> for m
  have t4inj: "x = y" if "t4 x = t4 y" for x y
  proof (rule ccontr)
    obtain i  j  k  l  where x: "x = (i,j,k,l)" by (meson prod_cases4) 
    obtain i' j' k' l' where y: "y = (i',j',k',l')" by (meson prod_cases4) 
    have 1: "bra (i,k) *\<^sub>V t4 x *\<^sub>V ket (j,l) = 1"
      by (auto simp: bra_def t4_def x tensor_op_state butter_def times_applyOp ket_Kronecker_delta_eq
               simp flip: tensor_state_ket)
    assume \<open>x \<noteq> y\<close>
    then have 2: "bra (i,k) *\<^sub>V t4 y *\<^sub>V ket (j,l) = 0"
      by (auto simp: bra_def t4_def x y tensor_op_state butter_def times_applyOp ket_Kronecker_delta_neq
               simp flip: tensor_state_ket)
    from 1 2 that
    show False
      by auto
  qed
  have \<open>\<phi> (tensor_maps (butter i j) (butter k l)) = F2 (butter i j) (butter k l)\<close> for i j k l
    apply (subst asm_rl[of \<open>tensor_maps (butter i j) (butter k l) = t4 (i,j,k,l)\<close>])
     apply (simp add: t4_def)
    by (auto simp add: injI t4inj inv_f_f \<phi>_def)

  have *: \<open>range t4 = {tensor_op (butter i j) (butter k l) |i j k l. True}\<close>
    apply (auto simp: case_prod_beta t4_def)
    using image_iff by fastforce

  have "cblinfun_extension_exists (range t4) \<phi>"
    apply (rule cblinfun_extension_exists_finite)
    apply auto unfolding * 
    using cindependent_tensor_op
    using cspan_tensor_op
    by auto

  then obtain G where G: \<open>G *\<^sub>V (t4 (i,j,k,l)) = F2 (butter i j) (butter k l)\<close> for i j k l
    apply atomize_elim
    unfolding cblinfun_extension_exists_def
    apply auto
    by (metis (no_types, lifting) t4inj \<phi>_def f_inv_into_f rangeI split_conv)

  have *: \<open>G *\<^sub>V tensor_maps (butter i j) (butter k l) = F2 (butter i j) (butter k l)\<close> for i j k l
    using G by (auto simp: t4_def)
  have *: \<open>G *\<^sub>V tensor_maps a (butter k l) = F2 a (butter k l)\<close> for a k l
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>\<lambda>a. F2 a _\<close> and B=\<open>{butter k l|k l. True}\<close>])
    unfolding linfun_cspan
    using * apply (auto intro!: linear_compose[unfolded o_def, where f=\<open>\<lambda>a. tensor_maps a _\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (metis cbilinear_def tensor_maps_cbilinear)
    apply (simp add: cblinfun_apply_add clinearI)
    using assms unfolding cbilinear_def by blast
  have G_F2: \<open>G *\<^sub>V tensor_maps a b = F2 a b\<close> for a b
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>F2 a\<close> and B=\<open>{butter k l|k l. True}\<close>])
    unfolding linfun_cspan
    using * apply (auto simp: cblinfun_apply_add clinearI
                        intro!: linear_compose[unfolded o_def, where f=\<open>tensor_maps a\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (meson cbilinear_def tensor_maps_cbilinear)
    using assms unfolding cbilinear_def by blast

  have \<open>clinear F2' \<and> (\<forall>a b. F2' (tensor_maps a b) = F2 a b)\<close>
    unfolding F2'_def tensor_lift_def 
    apply (rule someI[where x=\<open>(*\<^sub>V) G\<close> and P=\<open>\<lambda>G. clinear G \<and> (\<forall>a b. G (tensor_maps a b) = F2 a b)\<close>])
    using G_F2 by (simp add: cblinfun_apply_add clinearI)

  then show \<open>maps_hom F2'\<close> and \<open>(\<lambda>a b. tensor_lift F2 (tensor_maps a b)) = F2\<close>
    unfolding F2'_def by auto
qed

lemma tensor_uniqueness: \<open>maps_2hom F2 \<Longrightarrow> maps_hom F \<Longrightarrow> (\<lambda>a b. F (tensor_maps a b)) = F2 \<Longrightarrow> F = tensor_lift F2\<close>
  using tensor_extensionality tensor_lift_hom tensor_existence by metis

lift_definition assoc_state0 :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite) ell2 \<Rightarrow> ('a\<times>('b\<times>'c)) ell2\<close> is
  \<open>\<lambda>f (a,(b,c)). f ((a,b),c)\<close>
  by auto

lift_definition assoc_state0' :: \<open>('a::finite\<times>('b::finite\<times>'c::finite)) ell2 \<Rightarrow> (('a\<times>'b)\<times>'c) ell2\<close> is
  \<open>\<lambda>f ((a,b),c). f (a,(b,c))\<close>
  by auto

lift_definition assoc_state :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>('b\<times>'c)) ell2\<close>
  is assoc_state0
  apply (rule cbounded_linear_finite_ell2)
  apply (rule clinearI; transfer)
  by auto

lift_definition assoc_state' :: \<open>('a::finite\<times>('b::finite\<times>'c::finite)) ell2 \<Rightarrow>\<^sub>C\<^sub>L (('a\<times>'b)\<times>'c) ell2\<close> is
  assoc_state0'
  apply (rule cbounded_linear_finite_ell2)
  apply (rule clinearI; transfer)
  by auto

lemma assoc_state_tensor: \<open>assoc_state *\<^sub>V tensor_state (tensor_state a b) c = tensor_state a (tensor_state b c)\<close>
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun_apply_add clinearI tensor_state_add1 tensor_state_scaleC1)
   apply (simp add: clinear_tensor_state2)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun_apply_add clinearI tensor_state_add1 tensor_state_add2 tensor_state_scaleC1 tensor_state_scaleC2)
   apply (simp add: clinearI tensor_state_add1 tensor_state_add2 tensor_state_scaleC1 tensor_state_scaleC2)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun_apply_add clinearI tensor_state_add2 tensor_state_scaleC2)
   apply (simp add: clinearI tensor_state_add2 tensor_state_scaleC2)
  unfolding assoc_state.rep_eq
  apply transfer
  by auto

lemma assoc_state'_tensor: \<open>assoc_state' *\<^sub>V tensor_state a (tensor_state b c) = tensor_state (tensor_state a b) c\<close>
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun_apply_add clinearI tensor_state_add1 tensor_state_scaleC1)
   apply (simp add: clinearI tensor_state_add1 tensor_state_scaleC1)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun_apply_add clinearI tensor_state_add1 tensor_state_add2 tensor_state_scaleC1 tensor_state_scaleC2)
   apply (simp add: clinearI tensor_state_add1 tensor_state_add2 tensor_state_scaleC1 tensor_state_scaleC2)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun_apply_add clinearI tensor_state_add2 tensor_state_scaleC2)
   apply (simp add: clinearI tensor_state_add2 tensor_state_scaleC2)
  unfolding assoc_state'.rep_eq
  apply transfer
  by auto

definition assoc :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite, 'a\<times>('b\<times>'c)) maps_hom\<close> where
  \<open>assoc a = assoc_state o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L assoc_state'\<close>

lemma assoc_hom: \<open>maps_hom assoc\<close>
  unfolding assoc_def
  by (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 clinearI)

lemma assoc_apply: \<open>assoc (tensor_maps (tensor_maps a b) c) = tensor_maps a (tensor_maps b c)\<close>
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: assoc_def times_applyOp tensor_op_state assoc_state_tensor assoc_state'_tensor flip: tensor_state_ket)


definition lvalue :: \<open>('a, 'b) maps_hom \<Rightarrow> bool\<close> where
  "lvalue F \<longleftrightarrow> 
     maps_hom F
   \<and> F idOp = idOp 
   \<and> (\<forall>a b. F(a o\<^sub>C\<^sub>L b) = F a o\<^sub>C\<^sub>L F b)
   \<and> (\<forall>a. F (a*) = (F a)*)"


lemma lvalue_hom: "lvalue F \<Longrightarrow> maps_hom F"
  for F :: "('a,'b) maps_hom" and G :: "('b,'c) maps_hom"
  unfolding lvalue_def by simp

lemma lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"
  for F :: "('a,'b) maps_hom" and G :: "('b,'c) maps_hom" 
  unfolding lvalue_def
  apply auto
  using comp_maps_hom by blast

lemma lvalue_mult: "lvalue F \<Longrightarrow> F (comp_domain a b) = comp_domain (F a) (F b)"
  for F :: "('a,'b) maps_hom" and G :: "('b,'c) maps_hom" 
  unfolding lvalue_def
  by auto

lemma pair_lvalue_axiom: 
  fixes F :: \<open>('a::finite, 'c) maps_hom\<close> and G :: \<open>('b::finite, 'c) maps_hom\<close>
  assumes \<open>lvalue F\<close> and \<open>lvalue G\<close> and [simp]: \<open>maps_hom p\<close>
  assumes compat: \<open>\<And>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
  assumes tensor: \<open>\<And>a b. p (tensor_op a b) = F a o\<^sub>C\<^sub>L G b\<close>
  shows \<open>lvalue p\<close>
proof (unfold lvalue_def, intro conjI allI)
  have h1: \<open>maps_hom (\<lambda>a. p (a o\<^sub>C\<^sub>L b))\<close> for b
    apply (rule comp_maps_hom[unfolded o_def, of _ p])
     apply (simp add: cblinfun_apply_dist1 clinearI)
    by simp
  have h2: \<open>maps_hom (\<lambda>a. p a o\<^sub>C\<^sub>L p b)\<close> for b
    apply (rule comp_maps_hom[unfolded o_def, of p])
    apply simp
    by (meson cblinfun_apply_dist1 clinearI scalar_op_op)
  have h3: \<open>maps_hom (\<lambda>c. p (d o\<^sub>C\<^sub>L c))\<close> for d
    apply (rule comp_maps_hom[unfolded o_def, of _ p])
     apply (simp add: cblinfun_apply_dist2 clinearI)
    by simp
  have h4: \<open>maps_hom (\<lambda>c. p d o\<^sub>C\<^sub>L p c)\<close> for d
    apply (rule comp_maps_hom[unfolded o_def, of p])
    apply simp
    by (simp add: cblinfun_apply_dist2 clinearI)

  fix x y :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  show "maps_hom p"
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

  have hom_padjadj: \<open>maps_hom (\<lambda>a. p (a*)*)\<close>
    using \<open>maps_hom p\<close>
    by (auto simp: Adj_cblinfun_plus complex_vector.linear_add complex_vector.linear_scale intro!: clinearI)

  have *: \<open>(p (tensor_op a b*))* = p (tensor_op a b)\<close> for a b
    using \<open>lvalue F\<close> \<open>lvalue G\<close>
    by (simp add: compat tensor tensor_op_adjoint lvalue_def)
  have \<open>(p (x*))* = p x\<close>
    apply (rule fun_cong[where x=x])
    apply (rule tensor_extensionality)
    using hom_padjadj * by simp_all
  then show \<open>p (x*) = (p x)*\<close>
    by (metis adjoint_twice)
qed

end
