section \<open>Tensor products (finite dimensional)\<close>

theory Finite_Tensor_Product
  imports Bounded_Operators.Complex_L2 Misc
begin

declare cblinfun.scaleC_right[simp]

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)

lift_definition tensor_ell2 :: \<open>'a::finite ell2 \<Rightarrow> 'b::finite ell2 \<Rightarrow> ('a\<times>'b) ell2\<close> (infixr "\<otimes>\<^sub>s" 70) is
  \<open>\<lambda>\<psi> \<phi> (i,j). \<psi> i * \<phi> j\<close>
  by simp

lemma tensor_ell2_add2: \<open>tensor_ell2 a (b + c) = tensor_ell2 a b + tensor_ell2 a c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (meson algebra_simps)

lemma tensor_ell2_add1: \<open>tensor_ell2 (a + b) c = tensor_ell2 a c + tensor_ell2 b c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (simp add: vector_space_over_itself.scale_left_distrib)

lemma tensor_ell2_scaleC2: \<open>tensor_ell2 a (c *\<^sub>C b) = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_scaleC1: \<open>tensor_ell2 (c *\<^sub>C a) b = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_inner_prod[simp]: \<open>\<langle>tensor_ell2 a b, tensor_ell2 c d\<rangle> = \<langle>a,c\<rangle> * \<langle>b,d\<rangle>\<close>
  apply transfer
  by (auto simp: case_prod_beta sum_product sum.cartesian_product mult.assoc mult.left_commute)

lemma clinear_tensor_ell21: "clinear (\<lambda>b. tensor_ell2 a b)"
  apply (rule clinearI; transfer)
  apply (auto simp: case_prod_beta)
  by (simp add: cond_case_prod_eta algebra_simps)

lemma clinear_tensor_ell22: "clinear (\<lambda>a. tensor_ell2 a b)"
  apply (rule clinearI; transfer)
  apply (auto simp: case_prod_beta)
  by (simp add: case_prod_beta' algebra_simps)

lemma tensor_ell2_ket[simp]: "tensor_ell2 (ket i) (ket j) = ket (i,j)"
  apply transfer by auto


definition tensor_op :: \<open>('a ell2, 'b::finite ell2) cblinfun \<Rightarrow> ('c ell2, 'd::finite ell2) cblinfun
      \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) cblinfun\<close> (infixr "\<otimes>\<^sub>o" 70) where
  \<open>tensor_op M N = (SOME P. \<forall>a c. P *\<^sub>V (ket (a,c))
      = tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c))\<close>

lemma tensor_op_ket: 
  fixes a :: \<open>'a::finite\<close> and b :: \<open>'b\<close> and c :: \<open>'c::finite\<close> and d :: \<open>'d\<close>
  shows \<open>tensor_op M N *\<^sub>V (ket (a,c)) = tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c)\<close>
proof -
  define S :: \<open>('a\<times>'c) ell2 set\<close> where "S = ket ` UNIV"
  define \<phi> where \<open>\<phi> = (\<lambda>(a,c). tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c))\<close>
  define \<phi>' where \<open>\<phi>' = \<phi> \<circ> inv ket\<close>

  have def: \<open>tensor_op M N = (SOME P. \<forall>a c. P *\<^sub>V (ket (a,c)) = \<phi> (a,c))\<close>
    unfolding tensor_op_def \<phi>_def by auto

  have \<open>cindependent S\<close>
    using S_def cindependent_ket by blast
  moreover have \<open>cspan S = UNIV\<close>
    using S_def cspan_ket_finite by blast
  ultimately have "cblinfun_extension_exists S \<phi>'"
    by (rule cblinfun_extension_exists_finite_dim)
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


lemma tensor_op_ell2: "tensor_op A B *\<^sub>V tensor_ell2 \<psi> \<phi> = tensor_ell2 (A *\<^sub>V \<psi>) (B *\<^sub>V \<phi>)"
proof -
  have 1: \<open>clinear (\<lambda>a. tensor_op A B *\<^sub>V tensor_ell2 a (ket b))\<close> for b
    by (auto intro!: clinearI simp: tensor_ell2_add1 tensor_ell2_scaleC1 cblinfun.add_right)
  have 2: \<open>clinear (\<lambda>a. tensor_ell2 (A *\<^sub>V a) (B *\<^sub>V ket b))\<close> for b
    by (auto intro!: clinearI simp: tensor_ell2_add1 tensor_ell2_scaleC1 cblinfun.add_right)
  have 3: \<open>clinear (\<lambda>a. tensor_op A B *\<^sub>V tensor_ell2 \<psi> a)\<close>
    by (auto intro!: clinearI simp: tensor_ell2_add2 tensor_ell2_scaleC2 cblinfun.add_right)
  have 4: \<open>clinear (\<lambda>a. tensor_ell2 (A *\<^sub>V \<psi>) (B *\<^sub>V a))\<close>
    by (auto intro!: clinearI simp: tensor_ell2_add2 tensor_ell2_scaleC2 cblinfun.add_right)

  have eq_ket_ket: \<open>tensor_op A B *\<^sub>V tensor_ell2 (ket a) (ket b) = tensor_ell2 (A *\<^sub>V ket a) (B *\<^sub>V ket b)\<close> for a b
    by (simp add: tensor_op_ket)
  have eq_ket: \<open>tensor_op A B *\<^sub>V tensor_ell2 \<psi> (ket b) = tensor_ell2 (A *\<^sub>V \<psi>) (B *\<^sub>V ket b)\<close> for b
    apply (rule fun_cong[where x=\<psi>])
    using 1 2 eq_ket_ket by (rule clinear_equal_ket)
  show ?thesis 
    apply (rule fun_cong[where x=\<phi>])
    using 3 4 eq_ket by (rule clinear_equal_ket)
qed

lemma comp_tensor_op: "(tensor_op a b) o\<^sub>C\<^sub>L (tensor_op c d) = tensor_op (a o\<^sub>C\<^sub>L c) (b o\<^sub>C\<^sub>L d)"
  for a :: "'e::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2" and b :: "'f::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2" and
  c :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'e ell2" and d :: "'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'f ell2"
  apply (rule equal_ket)
  apply (rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2 cblinfun_apply_cblinfun_compose)


lemma tensor_op_cbilinear: \<open>cbilinear (tensor_op :: 'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2
                                                 \<Rightarrow> 'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2 \<Rightarrow> _)\<close>
proof -
  have \<open>clinear (\<lambda>b::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. tensor_op a b)\<close> for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    apply (rule clinearI)
     apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
     apply (simp flip: tensor_ell2_ket add: tensor_op_ell2 cblinfun.add_left tensor_ell2_add2)
    apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
    by (simp add: scaleC_cblinfun.rep_eq tensor_ell2_scaleC2 tensor_op_ket)

  moreover have \<open>clinear (\<lambda>a::'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2. tensor_op a b)\<close> for b :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
    apply (rule clinearI)
     apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
     apply (simp flip: tensor_ell2_ket add: tensor_op_ell2 cblinfun.add_left tensor_ell2_add1)
    apply (rule equal_ket, rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
    by (simp add: scaleC_cblinfun.rep_eq tensor_ell2_scaleC1 tensor_op_ket)

  ultimately show ?thesis
    unfolding cbilinear_def by auto
qed


lemma tensor_butter: \<open>tensor_op (butterket i j) (butterket k l) = butterket (i,k) (j,l)\<close>
  for i :: "_" and j :: "_::finite" and k :: "_" and l :: "_::finite"
  apply (rule equal_ket, rename_tac x, case_tac x)
  apply (auto simp flip: tensor_ell2_ket simp: cblinfun_apply_cblinfun_compose tensor_op_ell2 butterfly_def)
  by (auto simp: tensor_ell2_scaleC1 tensor_ell2_scaleC2)

lemma cspan_tensor_op: \<open>cspan {tensor_op (butterket i j) (butterket k l)| i (j::_::finite) k (l::_::finite). True} = UNIV\<close>
  unfolding tensor_butter
  apply (subst linfun_cspan[symmetric])
  by (metis surj_pair)

lemma cindependent_tensor_op: \<open>cindependent {tensor_op (butterket i j) (butterket k l)| i (j::_::finite) k (l::_::finite). True}\<close>
  unfolding tensor_butter
  using linfun_cindependent
  by (smt (z3) Collect_mono_iff complex_vector.independent_mono)


lemma tensor_extensionality:
  fixes F G :: \<open>((('a::finite \<times> 'b::finite) ell2) \<Rightarrow>\<^sub>C\<^sub>L (('c::finite \<times> 'd::finite) ell2)) \<Rightarrow> 'e::complex_vector\<close>
  assumes [simp]: "clinear F" "clinear G"
  assumes tensor_eq: "(\<And>a b. F (tensor_op a b) = G (tensor_op a b))"
  shows "F = G"
proof (rule ext, rule complex_vector.linear_eq_on_span[where f=F and g=G])
  show \<open>clinear F\<close> and \<open>clinear G\<close>
    using assms by (simp_all add: cbilinear_def)
  show \<open>x \<in> cspan  {tensor_op (butterket i j) (butterket k l)| i j k l. True}\<close> 
    for x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2\<close>
    using cspan_tensor_op by auto
  show \<open>F x = G x\<close> if \<open>x \<in> {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close> for x
    using that by (auto simp: tensor_eq)
qed

lemma tensor_id[simp]: \<open>tensor_op id_cblinfun id_cblinfun = id_cblinfun\<close>
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2)

lemma tensor_op_adjoint: \<open>(tensor_op a b)* = tensor_op (a*) (b*)\<close>
  apply (rule cinner_ket_adjointI[symmetric])
  apply (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)
  by (simp add: cinner_adj_left)

lemma tensor_butterfly[simp]: "tensor_op (butterfly \<psi> \<psi>') (butterfly \<phi> \<phi>') = butterfly (tensor_ell2 \<psi> \<phi>) (tensor_ell2 \<psi>' \<phi>')"
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2 butterfly_def
      cblinfun_apply_cblinfun_compose tensor_ell2_scaleC1 tensor_ell2_scaleC2)

(* TODO move to BO library misc *)
instance prod :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (simp add: CARD_1)

(* TODO move to BO library *)
instance cblinfun :: (\<open>{cfinite_dim,complex_normed_vector}\<close>, \<open>{cfinite_dim,complex_normed_vector}\<close>) cfinite_dim
  sorry

definition tensor_lift :: \<open>(('a1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a2::finite ell2) \<Rightarrow> ('b1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2::finite ell2) \<Rightarrow> 'c)
                        \<Rightarrow> ((('a1\<times>'b1) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a2\<times>'b2) ell2) \<Rightarrow> 'c::complex_vector)\<close> where
  "tensor_lift F2 = (SOME G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b))"

lemma 
  fixes F2 :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2
            \<Rightarrow> 'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2
            \<Rightarrow> 'e::complex_normed_vector"
  assumes "cbilinear F2"
  shows tensor_lift_clinear: "clinear (tensor_lift F2)"
  and tensor_lift_correct:  \<open>(\<lambda>a b. tensor_lift F2 (tensor_op a b)) = F2\<close>
proof -
  define F2' t4 \<phi> where
    \<open>F2' = tensor_lift F2\<close> and
    \<open>t4 = (\<lambda>(i,j,k,l). tensor_op (butterket i j) (butterket k l))\<close> and
    \<open>\<phi> m = (let (i,j,k,l) = inv t4 m in F2 (butterket i j) (butterket k l))\<close> for m
  have t4inj: "x = y" if "t4 x = t4 y" for x y
  proof (rule ccontr)
    obtain i  j  k  l  where x: "x = (i,j,k,l)" by (meson prod_cases4) 
    obtain i' j' k' l' where y: "y = (i',j',k',l')" by (meson prod_cases4) 
    have 1: "bra (i,k) *\<^sub>V t4 x *\<^sub>V ket (j,l) = 1"
      by (auto simp: t4_def x tensor_op_ell2 butterfly_def cblinfun_apply_cblinfun_compose ket_Kronecker_delta_eq
               simp flip: tensor_ell2_ket)
    assume \<open>x \<noteq> y\<close>
    then have 2: "bra (i,k) *\<^sub>V t4 y *\<^sub>V ket (j,l) = 0"
      by (auto simp: t4_def x y tensor_op_ell2 butterfly_def cblinfun_apply_cblinfun_compose ket_Kronecker_delta_neq
               simp flip: tensor_ell2_ket)
    from 1 2 that
    show False
      by auto
  qed
  have \<open>\<phi> (tensor_op (butterket i j) (butterket k l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply (subst asm_rl[of \<open>tensor_op (butterket i j) (butterket k l) = t4 (i,j,k,l)\<close>])
     apply (simp add: t4_def)
    by (auto simp add: injI t4inj inv_f_f \<phi>_def)

  have *: \<open>range t4 = {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close>
    apply (auto simp: case_prod_beta t4_def)
    using image_iff by fastforce

  have "cblinfun_extension_exists (range t4) \<phi>"
    thm cblinfun_extension_exists_finite_dim[where \<phi>=\<phi>]
    apply (rule cblinfun_extension_exists_finite_dim)
    apply auto unfolding * 
    using cindependent_tensor_op
    using cspan_tensor_op
    by auto

  then obtain G where G: \<open>G *\<^sub>V (t4 (i,j,k,l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply atomize_elim
    unfolding cblinfun_extension_exists_def
    apply auto
    by (metis (no_types, lifting) t4inj \<phi>_def f_inv_into_f rangeI split_conv)

  have *: \<open>G *\<^sub>V tensor_op (butterket i j) (butterket k l) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    using G by (auto simp: t4_def)
  have *: \<open>G *\<^sub>V tensor_op a (butterket k l) = F2 a (butterket k l)\<close> for a k l
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>\<lambda>a. F2 a _\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding linfun_cspan
    using * apply (auto intro!: clinear_compose[unfolded o_def, where f=\<open>\<lambda>a. tensor_op a _\<close> and g=\<open>(*\<^sub>V) G\<close>])
     apply (metis cbilinear_def tensor_op_cbilinear)
    using bounded_clinear.axioms(1) cblinfun_apply apply blast
    using assms unfolding cbilinear_def by blast
  have G_F2: \<open>G *\<^sub>V tensor_op a b = F2 a b\<close> for a b
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>F2 a\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding linfun_cspan
    using * apply (auto simp: cblinfun.add_right clinearI
                        intro!: clinear_compose[unfolded o_def, where f=\<open>tensor_op a\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (meson cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast

  have \<open>clinear F2' \<and> (\<forall>a b. F2' (tensor_op a b) = F2 a b)\<close>
    unfolding F2'_def tensor_lift_def 
    apply (rule someI[where x=\<open>(*\<^sub>V) G\<close> and P=\<open>\<lambda>G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b)\<close>])
    using G_F2 by (simp add: cblinfun.add_right clinearI)

  then show \<open>clinear F2'\<close> and \<open>(\<lambda>a b. tensor_lift F2 (tensor_op a b)) = F2\<close>
    unfolding F2'_def by auto
qed

lift_definition assoc_ell20 :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite) ell2 \<Rightarrow> ('a\<times>('b\<times>'c)) ell2\<close> is
  \<open>\<lambda>f (a,(b,c)). f ((a,b),c)\<close>
  by auto

lift_definition assoc_ell20' :: \<open>('a::finite\<times>('b::finite\<times>'c::finite)) ell2 \<Rightarrow> (('a\<times>'b)\<times>'c) ell2\<close> is
  \<open>\<lambda>f ((a,b),c). f (a,(b,c))\<close>
  by auto

lift_definition assoc_ell2 :: \<open>(('a::finite\<times>'b::finite)\<times>'c::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>('b\<times>'c)) ell2\<close>
  is assoc_ell20
  apply (subst bounded_clinear_finite_dim)
  apply (rule clinearI; transfer)
  by auto

lift_definition assoc_ell2' :: \<open>('a::finite\<times>('b::finite\<times>'c::finite)) ell2 \<Rightarrow>\<^sub>C\<^sub>L (('a\<times>'b)\<times>'c) ell2\<close> is
  assoc_ell20'
  apply (subst bounded_clinear_finite_dim)
  apply (rule clinearI; transfer)
  by auto

lemma assoc_ell2_tensor: \<open>assoc_ell2 *\<^sub>V tensor_ell2 (tensor_ell2 a b) c = tensor_ell2 a (tensor_ell2 b c)\<close>
  apply (rule clinear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinear_tensor_ell22)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
  unfolding assoc_ell2.rep_eq
  apply transfer
  by auto

lemma assoc_ell2'_tensor: \<open>assoc_ell2' *\<^sub>V tensor_ell2 a (tensor_ell2 b c) = tensor_ell2 (tensor_ell2 a b) c\<close>
  apply (rule clinear_equal_ket[THEN fun_cong, where x=a])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_scaleC1)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=b])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add1 tensor_ell2_add2 tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  apply (rule clinear_equal_ket[THEN fun_cong, where x=c])
    apply (simp add: cblinfun.add_right clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
   apply (simp add: clinearI tensor_ell2_add2 tensor_ell2_scaleC2)
  unfolding assoc_ell2'.rep_eq
  apply transfer
  by auto

lemma adjoint_assoc_ell2[simp]: \<open>assoc_ell2* = assoc_ell2'\<close>
proof (rule adjoint_eqI[symmetric])
  have [simp]: \<open>clinear (cinner (assoc_ell2' *\<^sub>V x))\<close> for x :: \<open>('a \<times> 'b \<times> 'c) ell2\<close>
    by (metis (no_types, lifting) cblinfun.add_right cinner_scaleC_right clinearI complex_scaleC_def mult.comm_neutral of_complex_def vector_to_cblinfun_adj_apply)
  have [simp]: \<open>clinear (\<lambda>a. \<langle>x, assoc_ell2 *\<^sub>V a\<rangle>)\<close> for x :: \<open>('a \<times> 'b \<times> 'c) ell2\<close>
    by (simp add: cblinfun.add_right cinner_add_right clinearI)
  have [simp]: \<open>antilinear (\<lambda>a. \<langle>a, y\<rangle>)\<close> for y :: \<open>('a \<times> 'b \<times> 'c) ell2\<close>
    using bounded_antilinear_cinner_left bounded_antilinear_def by blast
  have [simp]: \<open>antilinear (\<lambda>a. \<langle>assoc_ell2' *\<^sub>V a, y\<rangle>)\<close> for y :: \<open>(('a \<times> 'b) \<times> 'c) ell2\<close>
    by (simp add: cblinfun.add_right cinner_add_left antilinearI)
  have \<open>\<langle>assoc_ell2' *\<^sub>V (ket x), ket y\<rangle> = \<langle>ket x, assoc_ell2 *\<^sub>V ket y\<rangle>\<close> for x :: \<open>'a \<times> 'b \<times> 'c\<close> and y
    apply (cases x, cases y)
    by (simp flip: tensor_ell2_ket add: assoc_ell2'_tensor assoc_ell2_tensor)
  then have \<open>\<langle>assoc_ell2' *\<^sub>V (ket x), y\<rangle> = \<langle>ket x, assoc_ell2 *\<^sub>V y\<rangle>\<close> for x :: \<open>'a \<times> 'b \<times> 'c\<close> and y
    by (rule clinear_equal_ket[THEN fun_cong, rotated 2], simp_all)
  then show \<open>\<langle>assoc_ell2' *\<^sub>V x, y\<rangle> = \<langle>x, assoc_ell2 *\<^sub>V y\<rangle>\<close> for x :: \<open>('a \<times> 'b \<times> 'c) ell2\<close> and y
    by (rule antilinear_equal_ket[THEN fun_cong, rotated 2], simp_all)
qed

lemma adjoint_assoc_ell2'[simp]: \<open>assoc_ell2'* = assoc_ell2\<close>
  by (simp flip: adjoint_assoc_ell2)

lemma tensor_ell2_extensionality:
  assumes "(\<And>s t. a *\<^sub>V (s \<otimes>\<^sub>s t) = b *\<^sub>V (s \<otimes>\<^sub>s t))"
  shows "a = b"
  apply (rule equal_ket, case_tac x, hypsubst_thin)
  by (simp add: assms flip: tensor_ell2_ket)

lemma assoc_ell2'_assoc_ell2[simp]: \<open>assoc_ell2' o\<^sub>C\<^sub>L assoc_ell2 = id_cblinfun\<close>
  by (auto intro!: equal_ket simp: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor simp flip: tensor_ell2_ket)

lemma assoc_ell2_assoc_ell2'[simp]: \<open>assoc_ell2 o\<^sub>C\<^sub>L assoc_ell2' = id_cblinfun\<close>
  by (auto intro!: equal_ket simp: cblinfun_apply_cblinfun_compose assoc_ell2'_tensor assoc_ell2_tensor simp flip: tensor_ell2_ket)

lemma unitary_assoc_ell2[simp]: "unitary assoc_ell2"
  unfolding unitary_def by auto

lemma unitary_assoc_ell2'[simp]: "unitary assoc_ell2'"
  unfolding unitary_def by auto

lemma tensor_op_left_add: \<open>(x + y) \<otimes>\<^sub>o b = x \<otimes>\<^sub>o b + y \<otimes>\<^sub>o b\<close>
  for x y :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add1 tensor_op_ket)

lemma tensor_op_right_add: \<open>b \<otimes>\<^sub>o (x + y) = b \<otimes>\<^sub>o x + b \<otimes>\<^sub>o y\<close>
  for x y :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add2 tensor_op_ket)

lemma tensor_op_scaleC_left: \<open>(c *\<^sub>C x) \<otimes>\<^sub>o b = c *\<^sub>C (x \<otimes>\<^sub>o b)\<close>
  for x :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (metis scaleC_cblinfun.rep_eq tensor_ell2_ket tensor_ell2_scaleC1 tensor_op_ell2)

lemma tensor_op_scaleC_right: \<open>b \<otimes>\<^sub>o (c *\<^sub>C x) = c *\<^sub>C (b \<otimes>\<^sub>o x)\<close>
  for x :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (metis scaleC_cblinfun.rep_eq tensor_ell2_ket tensor_ell2_scaleC2 tensor_op_ell2)

lemma clinear_tensor_left[simp]: \<open>clinear (\<lambda>a. a \<otimes>\<^sub>o b :: _::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _::finite ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_left_add)
  by (rule tensor_op_scaleC_left)

lemma clinear_tensor_right[simp]: \<open>clinear (\<lambda>b. a \<otimes>\<^sub>o b :: _::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _::finite ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_right_add)
  by (rule tensor_op_scaleC_right)

end
