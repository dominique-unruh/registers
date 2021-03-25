theory Quantum
  imports Jordan_Normal_Form.Matrix_Impl "HOL-Library.Rewrite"
          Bounded_Operators.Complex_L2
          Finite_Tensor_Products
begin


unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)


(* instantiation mat :: (conjugate) conjugate
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
  unfolding conjugate_mat_def by auto *)

(* lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto *)

(* lemma index_mat_fstsnd:  "fst x < nr \<Longrightarrow> snd x < nc \<Longrightarrow> mat nr nc f $$ x = f x"
  apply (cases x) by auto *)

(* definition tensor_pack :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat" where "tensor_pack X Y = (\<lambda>(x, y). x * Y + y)"
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
  by (metis (no_types, lifting) Euclidean_Division.div_eq_0_iff add_0_iff bits_mod_div_trivial div_mult_self4 mod_mult2_eq mod_mult_self1_is_0 mult.commute) *)

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


(* lemma tensor_op_conjugate[simp]: "tensor_op (conjugate_op a) (conjugate_op b) = conjugate_op (tensor_op a b)"
  apply transfer
  by (auto simp: conjugate_mat_def mat_eq_iff case_prod_beta) *)

(* lemma tensor_op_transpose[simp]: "tensor_op (transpose_op a) (transpose_op b) = transpose_op (tensor_op a b)"
  apply transfer
  by (auto simp: mat_eq_iff case_prod_beta) *)

(* lemma tensor_op_adjoint[simp]: "tensor_op (adjoint_op a) (adjoint_op b) = adjoint_op (tensor_op a b)"
  unfolding adjoint_op_def by simp *)

abbreviation tensor_maps :: \<open>'a::finite domain_end \<Rightarrow> 'b::finite domain_end \<Rightarrow> ('a\<times>'b) domain_end\<close> where
  \<open>tensor_maps \<equiv> tensor_op\<close>

lemma tensor_2hom: \<open>maps_2hom tensor_maps\<close>
  by (simp add: tensor_op_cbilinear)


(* ML \<open>
\<^term>\<open>{f x y | x y. P x y}\<close>
\<close> *)

(* TODO: move tensor stuff into Finite_Tensor_Product *)


definition tensor_lift :: \<open>('a::finite, 'b::finite, 'c) maps_2hom \<Rightarrow> (('a\<times>'b, 'c) maps_hom)\<close> where
  "tensor_lift F2 = (SOME G. clinear G \<and> (\<forall>a b. G (tensor_maps a b) = F2 a b))"

lemma assumes "maps_2hom F2"
  shows tensor_lift_hom: "maps_hom (tensor_lift F2)"
  and tensor_existence:  \<open>(\<lambda>a b. tensor_lift F2 (tensor_maps a b)) = F2\<close>
proof -
  define F2' t4 \<phi> where
    \<open>F2' = tensor_lift F2\<close> and
    \<open>t4 = (\<lambda>(i,j,k,l). tensor_maps (butterket i j) (butterket k l))\<close> and
    \<open>\<phi> m = (let (i,j,k,l) = inv t4 m in F2 (butterket i j) (butterket k l))\<close> for m
  have t4inj: "x = y" if "t4 x = t4 y" for x y
  proof (rule ccontr)
    obtain i  j  k  l  where x: "x = (i,j,k,l)" by (meson prod_cases4) 
    obtain i' j' k' l' where y: "y = (i',j',k',l')" by (meson prod_cases4) 
    have 1: "bra (i,k) *\<^sub>V t4 x *\<^sub>V ket (j,l) = 1"
      by (auto simp: bra_def t4_def x tensor_op_state butterfly_def' times_applyOp ket_Kronecker_delta_eq
               simp flip: tensor_ell2_ket)
    assume \<open>x \<noteq> y\<close>
    then have 2: "bra (i,k) *\<^sub>V t4 y *\<^sub>V ket (j,l) = 0"
      by (auto simp: bra_def t4_def x y tensor_op_state butterfly_def' times_applyOp ket_Kronecker_delta_neq
               simp flip: tensor_ell2_ket)
    from 1 2 that
    show False
      by auto
  qed
  have \<open>\<phi> (tensor_maps (butterket i j) (butterket k l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply (subst asm_rl[of \<open>tensor_maps (butterket i j) (butterket k l) = t4 (i,j,k,l)\<close>])
     apply (simp add: t4_def)
    by (auto simp add: injI t4inj inv_f_f \<phi>_def)

  have *: \<open>range t4 = {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close>
    apply (auto simp: case_prod_beta t4_def)
    using image_iff by fastforce

  have "cblinfun_extension_exists (range t4) \<phi>"
    apply (rule cblinfun_extension_exists_finite)
    apply auto unfolding * 
    using cindependent_tensor_op
    using cspan_tensor_op
    by auto

  then obtain G where G: \<open>G *\<^sub>V (t4 (i,j,k,l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply atomize_elim
    unfolding cblinfun_extension_exists_def
    apply auto
    by (metis (no_types, lifting) t4inj \<phi>_def f_inv_into_f rangeI split_conv)

  have *: \<open>G *\<^sub>V tensor_maps (butterket i j) (butterket k l) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    using G by (auto simp: t4_def)
  have *: \<open>G *\<^sub>V tensor_maps a (butterket k l) = F2 a (butterket k l)\<close> for a k l
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>\<lambda>a. F2 a _\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding linfun_cspan
    using * apply (auto intro!: linear_compose[unfolded o_def, where f=\<open>\<lambda>a. tensor_maps a _\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (metis cbilinear_def tensor_op_cbilinear)
    apply (simp add: cblinfun_apply_add clinearI)
    using assms unfolding cbilinear_def by blast
  have G_F2: \<open>G *\<^sub>V tensor_maps a b = F2 a b\<close> for a b
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>F2 a\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding linfun_cspan
    using * apply (auto simp: cblinfun_apply_add clinearI
                        intro!: linear_compose[unfolded o_def, where f=\<open>tensor_maps a\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (meson cbilinear_def tensor_op_cbilinear)
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

lemma assoc_state_tensor: \<open>assoc_state *\<^sub>V tensor_ell2 (tensor_ell2 a b) c = tensor_ell2 a (tensor_ell2 b c)\<close>
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinear_tensor_ell22)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
  unfolding assoc_state.rep_eq
  apply transfer
  by auto

lemma assoc_state'_tensor: \<open>assoc_state' *\<^sub>V tensor_ell2 a (tensor_ell2 b c) = tensor_ell2 (tensor_ell2 a b) c\<close>
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  apply (rule cbounded_linear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun_apply_add clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
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
  by (simp add: assoc_def times_applyOp tensor_op_state assoc_state_tensor assoc_state'_tensor flip: tensor_ell2_ket)


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

lemma lvalue_mult: "lvalue F \<Longrightarrow> comp_domain (F a) (F b) = F (comp_domain a b)"
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
