theory Quantum
  imports Jordan_Normal_Form.Matrix_Impl "HOL-Library.Rewrite"
 Jordan_Normal_Form.Matrix
begin


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

lemma row_conjugate_mat[simp]: \<open>i < dim_row A \<Longrightarrow> row (conjugate A) i = conjugate (row A i)\<close>
  unfolding conjugate_mat_def by auto

lemma col_conjugate_mat[simp]: \<open>i < dim_col A \<Longrightarrow> col (conjugate A) i = conjugate (col A i)\<close>
  unfolding conjugate_mat_def by auto

(* definition "adjoint_mat M = conjugate (transpose_mat M)"

lemma adjoint_carrier_mat[simp]: \<open>M \<in> carrier_mat n m \<Longrightarrow> adjoint_mat M \<in> carrier_mat m n\<close>
  unfolding adjoint_mat_def
  by auto *)

lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto

lemma index_mat_fstsnd:  "fst x < nr \<Longrightarrow> snd x < nc \<Longrightarrow> mat nr nc f $$ x = f x"
  apply (cases x) by auto

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






class domain = enum
instance prod :: (domain,domain) domain
  by intro_classes

typedef (overloaded) ('a::enum) state =
  \<open>carrier_vec CARD('a) :: complex vec set\<close>
  apply (rule exI[of _ \<open>zero_vec CARD('a)\<close>])
  by auto
setup_lifting type_definition_state

typedef (overloaded) ('a::enum, 'b::enum) operator =
  \<open>carrier_mat CARD('b) CARD('a) :: complex mat set\<close>
  apply (rule exI[of _ \<open>zero_mat CARD('b) CARD('a)\<close>])
  by auto
type_synonym 'a domain_end = \<open>('a,'a) operator\<close>
setup_lifting type_definition_operator

lift_definition id_operator :: \<open>('a::enum, 'a::enum) operator\<close> is "one_mat CARD('a)"
  by auto

lift_definition apply_operator :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> 'a state \<Rightarrow> 'b state\<close> is
  "mult_mat_vec"
  by auto

lift_definition comp_op :: "('b::enum,'c::enum) operator \<Rightarrow> ('a::enum,'b) operator \<Rightarrow> ('a,'c) operator"  is
  "times"
  by auto

lemma comp_id_op_left[simp]: "comp_op id_operator a = a"
  apply transfer by auto

abbreviation comp_domain :: "'a::domain domain_end \<Rightarrow> 'a domain_end \<Rightarrow> 'a domain_end" where
  "comp_domain \<equiv> comp_op"

lemma comp_domain_assoc: "comp_op (comp_op a b) c = comp_op a (comp_op b c)"
  apply transfer by auto

lemma comp_apply_operator[simp]:
 "apply_operator (comp_op A B) \<psi> = apply_operator A (apply_operator B \<psi>)"
  apply transfer
  by auto

lift_definition conjugate_op :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> ('a::enum, 'b::enum) operator\<close> is
  \<open>conjugate\<close>
  by auto

lemma conjugate_op_involution[simp]: "conjugate_op (conjugate_op A) = A"
  apply transfer by auto

lift_definition transpose_op :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> ('b::enum, 'a::enum) operator\<close> is
  \<open>transpose_mat\<close>
  by auto

definition adjoint_op :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> ('b::enum, 'a::enum) operator\<close> where
  \<open>adjoint_op M = conjugate_op (transpose_op M)\<close>

lemma comp_adjoint_op: "adjoint_op (comp_op A B) = comp_op (adjoint_op B) (adjoint_op A)"
  unfolding adjoint_op_def apply transfer
  apply (auto simp: mat_eq_iff conjugate_mat_def scalar_prod_def simp flip: map_mat_transpose)
  by (meson mult.commute)

typedef ('a,'b) superoperator = \<open>UNIV :: ('a\<times>'a, 'b\<times>'b) operator set\<close>
  by auto
setup_lifting type_definition_superoperator

(* Matrix to vector, in "reading order", first row len is 'a *)
lift_definition flatten_operator :: \<open>('a::enum,'b::enum) operator \<Rightarrow> ('b\<times>'a) state\<close> is
  \<open>\<lambda>M. vec CARD('b\<times>'a) (\<lambda>i. M $$ tensor_unpack CARD('b) CARD('a) i)\<close>
  by auto

lift_definition unflatten_operator :: \<open>('b\<times>'a) state \<Rightarrow> ('a::enum,'b::enum) operator\<close> is
  \<open>\<lambda>v. mat CARD('b) CARD('a) (\<lambda>(i,j). v $ tensor_pack CARD('b) CARD('a) (i,j))\<close>
  by auto

lift_definition apply_superop :: \<open>('a::enum,'b::enum) superoperator \<Rightarrow> ('a,'a) operator \<Rightarrow> ('b,'b) operator\<close> is
  \<open>\<lambda>(SO::('a\<times>'a, 'b\<times>'b) operator) M. unflatten_operator (apply_operator SO (flatten_operator M))\<close>
  by -

lift_definition comp_superop :: \<open>('b::enum, 'c::enum) superoperator \<Rightarrow> ('a::enum,'b) superoperator \<Rightarrow> ('a,'c) superoperator\<close> is
  \<open>\<lambda>A B. comp_op A B\<close>
  by -

lemma flatten_unflatten_operator[simp]: "flatten_operator (unflatten_operator M) = M"
  apply transfer unfolding vec_eq_iff
  by (auto simp: index_mat_fstsnd)

lemma comp_apply_superop[simp]: "apply_superop (comp_superop A B) \<psi> = apply_superop A (apply_superop B \<psi>)"
  apply transfer by auto

type_synonym ('a,'b) maps_hom = \<open>'a domain_end \<Rightarrow> 'b domain_end\<close>
definition maps_hom :: \<open>('a::enum,'b::enum) maps_hom \<Rightarrow> bool\<close> where
  "maps_hom F \<longleftrightarrow> (\<exists>M. F = apply_superop M)"

lemma comp_maps_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (G \<circ> F)"
  unfolding maps_hom_def 
  apply auto apply (rule exI[of _ "comp_superop _ _"])
  apply (rule ext)
  by auto
(* TODO category laws *)


lemma transpose_op_hom[simp]: \<open>maps_hom transpose_op\<close>
  sorry

type_synonym ('a,'b,'c) maps_2hom = \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> 'c domain_end\<close>
definition maps_2hom :: "('a::enum, 'b::enum, 'c::enum) maps_2hom \<Rightarrow> bool" where
  "maps_2hom F \<longleftrightarrow> (\<forall>a. maps_hom (F a)) \<and> (\<forall>b. maps_hom (\<lambda>a. F a b))"

axiomatization where comp_2hom: "maps_2hom comp_op"


lift_definition tensor_state :: \<open>('a::enum) state \<Rightarrow> ('b::enum) state \<Rightarrow> ('a\<times>'b) state\<close> is
  \<open>\<lambda>\<psi> \<phi>. vec (CARD('a)*CARD('b)) (\<lambda>i. 
       let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in \<psi> $ i1 * \<phi> $ i2)\<close>
  by simp

lift_definition tensor_op :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> ('c::enum, 'd::enum) operator 
                                 \<Rightarrow> ('a\<times>'c, 'b\<times>'d) operator\<close> is
  \<open>\<lambda>A B. mat (CARD('b)*CARD('d)) (CARD('a)*CARD('c)) 
      (\<lambda>(i,j). let (i1,i2) = tensor_unpack CARD('b) CARD('d) i in
               let (j1,j2) = tensor_unpack CARD('a) CARD('c) j in
               A $$ (i1, j1) * B $$ (i2, j2))\<close>
  by auto


lemma tensor_op_state: "apply_operator (tensor_op A B) (tensor_state \<psi> \<phi>)
  = tensor_state (apply_operator A \<psi>) (apply_operator B \<phi>)"
  apply transfer
  apply (auto simp: case_prod_beta Let_def sum_product vec_eq_iff scalar_prod_def mult_mat_vec_def)
  apply (rule sum.cong, simp)
  apply (rule sum.cong, simp)
  by auto

lemma comp_tensor_op: "comp_op (tensor_op a b) (tensor_op c d) = tensor_op (comp_op a c) (comp_op b d)"
  apply transfer
  apply (simp add: mat_eq_iff scalar_prod_def case_prod_beta Ball_def)
  apply (intro allI impI)
  unfolding sum_product
  apply (rule sum.cong, simp)
  apply (rule sum.cong, simp)
  by simp

lemma tensor_op_conjugate[simp]: "tensor_op (conjugate_op a) (conjugate_op b) = conjugate_op (tensor_op a b)"
  apply transfer
  by (auto simp: conjugate_mat_def mat_eq_iff case_prod_beta)

lemma tensor_op_transpose[simp]: "tensor_op (transpose_op a) (transpose_op b) = transpose_op (tensor_op a b)"
  apply transfer
  by (auto simp: mat_eq_iff case_prod_beta)

lemma tensor_op_adjoint[simp]: "tensor_op (adjoint_op a) (adjoint_op b) = adjoint_op (tensor_op a b)"
  unfolding adjoint_op_def by simp

abbreviation tensor_maps :: \<open>'a::enum domain_end \<Rightarrow> 'b::enum domain_end \<Rightarrow> ('a\<times>'b) domain_end\<close> where
  \<open>tensor_maps \<equiv> tensor_op\<close>


lift_definition tensor_left0 :: "('a::enum,'a) operator \<Rightarrow> ('b::enum \<times> 'b, ('a\<times>'b) \<times> ('a\<times>'b)) operator" is
  \<open>\<lambda>A::complex mat. mat CARD(('a\<times>'b) \<times> ('a\<times>'b)) CARD('b\<times>'b) (\<lambda>(i,j). 
    let (j1,j2) = tensor_unpack CARD('b) CARD('b) j in
    let (i1,i2) = tensor_unpack CARD('a\<times>'b) CARD('a\<times>'b) i in
    let (i1a,i1b) = tensor_unpack CARD('a) CARD('b) i1 in
    let (i2a,i2b) = tensor_unpack CARD('a) CARD('b) i2 in
    if i1b=j1 \<and> i2b=j2 then A $$ (i1a,i2a) else 0) :: complex mat\<close>
  by auto


lift_definition tensor_right0 :: "('b::enum,'b) operator \<Rightarrow> ('a::enum \<times> 'a, ('a\<times>'b) \<times> ('a\<times>'b)) operator" is
  \<open>\<lambda>B::complex mat. mat CARD(('a\<times>'b) \<times> ('a\<times>'b)) CARD('a\<times>'a) (\<lambda>(i,j). 
    let (j1,j2) = tensor_unpack CARD('a) CARD('a) j in
    let (i1,i2) = tensor_unpack CARD('a\<times>'b) CARD('a\<times>'b) i in
    let (i1a,i1b) = tensor_unpack CARD('a) CARD('b) i1 in
    let (i2a,i2b) = tensor_unpack CARD('a) CARD('b) i2 in
    if i1a=j1 \<and> i2a=j2 then B $$ (i1b,i2b) else 0) :: complex mat\<close>
  by auto

lift_definition tensor_left :: "('a::enum,'a) operator \<Rightarrow> ('b::enum,'a\<times>'b) superoperator" is
  tensor_left0.

lift_definition tensor_right :: "('b::enum,'b) operator \<Rightarrow> ('a::enum,'a\<times>'b) superoperator" is
  tensor_right0.

lemma tensor_left_tensor_maps: "apply_superop (tensor_left a) b = tensor_maps a b"
  apply (transfer fixing: a b)
  apply transfer
  apply (simp add: Let_def case_prod_beta mat_eq_iff vec_eq_iff scalar_prod_def)
  apply auto
  apply (subst sum_single[where i=\<open>snd (tensor_unpack CARD('a) CARD('b) _)\<close>])
    apply auto
  apply (subst sum_single[where i=\<open>snd (tensor_unpack CARD('a) CARD('b) _)\<close>])
  by auto

lemma tensor_right_tensor_maps: "apply_superop (tensor_right b) a = tensor_maps a b"
  apply (transfer fixing: a b)
  apply transfer
  apply (simp add: Let_def case_prod_beta mat_eq_iff vec_eq_iff scalar_prod_def)
  apply auto
  apply (subst sum_single[where i=\<open>fst (tensor_unpack CARD('a) CARD('b) _)\<close>])
    apply auto
  apply (subst sum_single[where i=\<open>fst (tensor_unpack CARD('a) CARD('b) _)\<close>])
  by auto

lemma tensor_2hom: \<open>maps_2hom tensor_maps\<close>
  unfolding maps_2hom_def maps_hom_def
  apply auto
   apply (rule exI[of _ \<open>tensor_left _\<close>])
   apply (rule ext)
   apply (subst tensor_left_tensor_maps, simp)
  apply (rule exI[of _ \<open>tensor_right _\<close>])
  apply (rule ext)
  by (subst tensor_right_tensor_maps, simp)

lemma tensor_extensionality:
  fixes F G :: \<open>('a::enum\<times>'b::enum, 'c::enum) maps_hom\<close>
  assumes [simp]: "maps_hom F" "maps_hom G"
  assumes "(\<And>a b. F (tensor_maps a b) = G (tensor_maps a b))"
  shows "F = G"
  sorry

lemma tensor_id[simp]: \<open>tensor_maps id_operator id_operator = id_operator\<close>
  apply transfer
  apply (auto simp: case_prod_beta mat_eq_iff)
  by (metis prod.expand tensor_pack_unpack)

definition tensor_lift :: \<open>('a::domain, 'b::domain, 'c::domain) maps_2hom
                            \<Rightarrow> (('a\<times>'b, 'c) maps_hom)\<close> where
(* TODO *)
  "tensor_lift = undefined"



lemma tensor_lift_hom: "maps_2hom F2 \<Longrightarrow> maps_hom (tensor_lift F2)"
  sorry
lemma tensor_existence:  \<open>maps_2hom F2 \<Longrightarrow> (\<lambda>a b. tensor_lift F2 (tensor_maps a b)) = F2\<close>
  sorry
lemma tensor_uniqueness: \<open>maps_2hom F2 \<Longrightarrow> maps_hom F \<Longrightarrow> (\<lambda>a b. F (tensor_maps a b)) = F2 \<Longrightarrow> F = tensor_lift F2\<close>
  sorry
(* Formalize the weak property instead *)


lift_definition assoc00 :: \<open>((('a::enum\<times>'b::enum)\<times>'c::enum) \<times> (('a\<times>'b)\<times>'c),
                            ('a\<times>('b\<times>'c)) \<times> ('a\<times>('b\<times>'c))) operator\<close> is
  \<open>one_mat (CARD('a)*CARD('b)*CARD('c)*CARD('a)*CARD('b)*CARD('c)) :: complex mat\<close>
  by auto

lift_definition assoc0 :: \<open>(('a::enum \<times> 'b::enum) \<times> 'c::enum, 'a \<times> ('b \<times> 'c)) superoperator\<close> is
  assoc00.

lift_definition assoc :: \<open>(('a::enum\<times>'b::enum)\<times>'c::enum, 'a\<times>('b\<times>'c)) maps_hom\<close> is
  \<open>id\<close>
  by auto

lemma assoc_hom: \<open>maps_hom assoc\<close>
  unfolding maps_hom_def
  apply (rule exI[of _ assoc0])
  apply (rule ext)
  apply transfer
  apply transfer
  apply (auto simp: mat_eq_iff mult.assoc[symmetric])
  apply (subst index_vec)
   apply (metis (no_types, lifting) UNIV_I class_semiring.m_assoc tensor_pack_bound)
  by simp




lemma assoc_apply: \<open>assoc (tensor_maps (tensor_maps a b) c) = (tensor_maps a (tensor_maps b c))\<close>
  apply transfer
  by (auto simp: case_prod_beta mat_eq_iff mult.assoc[symmetric] tensor_unpack_fstfst tensor_unpack_sndsnd tensor_unpack_fstsnd)

definition lvalue :: \<open>('a::enum, 'b::enum) maps_hom \<Rightarrow> bool\<close> where
  "lvalue F \<longleftrightarrow> 
     maps_hom F
   \<and> F id_operator = id_operator 
   \<and> (\<forall>a b. F(comp_op a b) = comp_op (F a) (F b))
   \<and> (\<forall>a. F(adjoint_op a) = adjoint_op (F a))"

lemma lvalue_hom: "lvalue F \<Longrightarrow> maps_hom F"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom"
  unfolding lvalue_def by simp

lemma lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom" 
  unfolding lvalue_def
  by (auto intro: comp_maps_hom)

lemma lvalue_mult: "lvalue F \<Longrightarrow> F (comp_domain a b) = comp_domain (F a) (F b)"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom" 
  unfolding lvalue_def
  by auto

lemma maps_hom_conjugate: 
  assumes \<open>maps_hom p\<close>
  shows \<open>maps_hom (conjugate_op \<circ> p \<circ> conjugate_op)\<close>
  sorry

lemma pair_lvalue_axiom: 
  fixes F :: \<open>('a::enum, 'c::enum) maps_hom\<close> and G :: \<open>('b::enum, 'c::enum) maps_hom\<close>
  assumes \<open>lvalue F\<close> and \<open>lvalue G\<close> and [simp]: \<open>maps_hom p\<close>
  assumes compat: \<open>\<And>a b. comp_op (F a) (G b) = comp_op (G b) (F a)\<close>
  assumes tensor: \<open>\<And>a b. p (tensor_op a b) = comp_op (F a) (G b)\<close>
  shows \<open>lvalue p\<close>
proof (unfold lvalue_def, intro conjI allI)
  fix x y :: \<open>('a \<times> 'b, 'a \<times> 'b) operator\<close>
  show "maps_hom p"
    using assms by auto
  show \<open>p id_operator = id_operator\<close>
    unfolding tensor_id[symmetric] tensor
    using \<open>lvalue F\<close> \<open>lvalue G\<close> unfolding lvalue_def by auto
  show \<open>p (comp_op x y) = comp_op (p x) (p y)\<close>
  proof -
    have \<open>p (comp_op (tensor_op a b) (tensor_op a' b')) 
          = comp_op (p (tensor_op a b)) (p  (tensor_op a' b'))\<close> for a b a' b'
    proof -
      have \<open>p (comp_op (tensor_op a b) (tensor_op a' b')) = p (tensor_op (comp_op a a') (comp_op b b'))\<close>
        unfolding comp_tensor_op by simp
      also have \<open>\<dots> = comp_op (F (comp_op a a')) (G (comp_op b b'))\<close>
        unfolding tensor by simp
      also have \<open>\<dots> = comp_op (comp_op (F a) (F a')) (comp_op (G b) (G b'))\<close>
        using \<open>lvalue F\<close> \<open>lvalue G\<close> unfolding lvalue_def by simp
      also have \<open>\<dots> = comp_op (comp_op (F a) (G b)) (comp_op (F a') (G b'))\<close>
        using compat comp_domain_assoc by metis
      also have \<open>\<dots> = comp_op (p (tensor_maps a b)) (p (tensor_maps a' b'))\<close>
        unfolding tensor by simp
      finally show ?thesis
        by -
    qed
    then have \<open>p (comp_op x (tensor_op a' b')) 
          = comp_op (p x) (p  (tensor_op a' b'))\<close> for a' b'
      apply (rule tensor_extensionality[THEN fun_cong, rotated -1])
       apply (rule comp_maps_hom[unfolded o_def, of _ p])
      using comp_2hom maps_2hom_def apply auto[2]
       apply (rule comp_maps_hom[unfolded o_def, of p])
      using comp_2hom maps_2hom_def by auto
    then show ?thesis
      apply (rule tensor_extensionality[THEN fun_cong, rotated -1])
       apply (rule comp_maps_hom[unfolded o_def, of _ p])
      using comp_2hom maps_2hom_def apply auto[2]
       apply (rule comp_maps_hom[unfolded o_def, of p])
      using comp_2hom maps_2hom_def by auto
  qed
  show \<open>p (adjoint_op x) = adjoint_op (p x)\<close>
  proof -
    have hom1: \<open>maps_hom (conjugate_op \<circ> p \<circ> adjoint_op)\<close>
    proof -
      have \<open>maps_hom ((conjugate_op \<circ> p \<circ> conjugate_op) \<circ> transpose_op)\<close>
        by (intro maps_hom_conjugate comp_maps_hom transpose_op_hom assms)
      then show ?thesis
        by (simp add: adjoint_op_def[abs_def] o_def)
    qed
    have hom2: \<open>maps_hom (conjugate_op \<circ> adjoint_op \<circ> p)\<close>
      unfolding adjoint_op_def o_def apply simp unfolding o_def[symmetric]
      by (intro comp_maps_hom transpose_op_hom assms)

    have \<open>(p \<circ> adjoint_op) (tensor_op a b) = (adjoint_op \<circ> p) (tensor_op a b)\<close> for a b
    proof -
      have \<open>(p \<circ> adjoint_op) (tensor_op a b) = p (tensor_op (adjoint_op a) (adjoint_op b))\<close>
        unfolding tensor_op_adjoint by simp
      also have \<open>... = comp_op (F (adjoint_op a)) (G (adjoint_op b))\<close>
        unfolding tensor by simp
      also have \<open>... = comp_op (adjoint_op (F a)) (adjoint_op (G b))\<close>
        using \<open>lvalue F\<close> \<open>lvalue G\<close> unfolding lvalue_def by simp
      also have \<open>... = adjoint_op (comp_op (G b) (F a))\<close>
        by (simp add: comp_adjoint_op)
      also have \<open>... = adjoint_op (comp_op (F a) (G b))\<close>
        using compat by simp
      also have \<open>... = adjoint_op (p (tensor_op a b))\<close>
        unfolding tensor by simp
      also have \<open>\<dots> = (adjoint_op \<circ> p) (tensor_op a b)\<close>
        by auto
      finally show ?thesis
        by-
    qed
    then have \<open>(conjugate_op \<circ> p \<circ> adjoint_op) (tensor_op a b) = (conjugate_op \<circ> adjoint_op \<circ> p) (tensor_op a b)\<close> for a b
      by simp
    then have \<open>conjugate_op \<circ> p \<circ> adjoint_op = conjugate_op \<circ> adjoint_op \<circ> p\<close>
      using hom1 hom2 by (rule tensor_extensionality[rotated -1])
    then have \<open>p \<circ> adjoint_op = adjoint_op \<circ> p\<close>
      by (metis (no_types, lifting) comp_assoc conjugate_op_involution fun.map_id0 id_apply isomorphism_expand)
    then show ?thesis
      unfolding o_def by metis
  qed
qed

end
