theory Quantum
  imports Jordan_Normal_Form.Matrix_Impl
begin


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

lift_definition apply_operator :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> 'a state \<Rightarrow> 'b state\<close> is
  "mult_mat_vec"
  by auto

lift_definition comp_op :: "('b::enum,'c::enum) operator \<Rightarrow> ('a::enum,'b) operator \<Rightarrow> ('a,'c) operator"  is
  "times"
  by auto

abbreviation comp_domain :: "'a::domain domain_end \<Rightarrow> 'a domain_end \<Rightarrow> 'a domain_end" where
  "comp_domain \<equiv> comp_op"

lemma comp_domain_assoc: "comp_domain (comp_domain a b) c = comp_domain a (comp_domain b c)"
  apply transfer by auto

lemma comp_apply_operator[simp]:
 "apply_operator (comp_op A B) \<psi> = apply_operator A (apply_operator B \<psi>)"
  apply transfer
  by auto

value "List.product [1,2,3] [8,9] :: (int*int) list"

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
definition maps_hom :: \<open>('a::domain,'b::domain) maps_hom \<Rightarrow> bool\<close> where
  "maps_hom F \<longleftrightarrow> (\<exists>M. F = apply_superop M)"

lemma comp_maps_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (G \<circ> F)"
  unfolding maps_hom_def 
  apply auto apply (rule exI[of _ "comp_superop _ _"])
  apply (rule ext)
  by auto
(* TODO category laws *)

type_synonym ('a,'b,'c) maps_2hom = \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> 'c domain_end\<close>
definition maps_2hom :: "('a::domain, 'b::domain, 'c::domain) maps_2hom \<Rightarrow> bool" where
  "maps_2hom F \<longleftrightarrow> (\<forall>a. maps_hom (F a)) \<and> (\<forall>b. maps_hom (\<lambda>a. F a b))"

axiomatization where comp_2hom: "maps_2hom comp_domain"


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
proof -
(* (* TODO: use tensor_pack_sum instead *)
  have split_sum: "(\<Sum>i = 0..<CARD('c) * CARD('d). f i)
      = (\<Sum>i = 0..<CARD('c). \<Sum>j = 0..<CARD('d). 
          f (tensor_pack CARD('c) CARD('d) (i, j)))" for f :: "_ \<Rightarrow> complex"
    apply (subst sum.cartesian_product) apply simp
    apply (subst sum.reindex[where h=\<open>tensor_pack CARD('c) CARD('d)\<close>, unfolded o_def, symmetric])
    by auto *)

  show ?thesis
    apply transfer
    apply (auto simp: case_prod_beta Let_def sum_product vec_eq_iff scalar_prod_def mult_mat_vec_def)
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    by auto
qed

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


definition tensor_lift :: \<open>('a::domain, 'b::domain, 'c::domain) maps_2hom
                            \<Rightarrow> (('a\<times>'b, 'c) maps_hom)\<close>

lemma tensor_lift_hom: "maps_2hom F2 \<Longrightarrow> maps_hom (tensor_lift F2)"
lemma tensor_existence:  \<open>maps_2hom F2 \<Longrightarrow> (\<lambda>a b. tensor_lift F2 (tensor_maps a b)) = F2\<close>
lemma tensor_uniqueness: \<open>maps_2hom F2 \<Longrightarrow> maps_hom F \<Longrightarrow> (\<lambda>a b. F (tensor_maps a b)) = F2 \<Longrightarrow> F = tensor_lift F2\<close>
(* Formalize the weak property instead *)

lift_definition assoc :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain, 'a\<times>('b\<times>'c)) maps_hom\<close> is
  \<open>id\<close>

lemma assoc_hom: \<open>maps_hom assoc\<close>
lemma assoc_apply: \<open>assoc (tensor_maps (tensor_maps a b) c) = (tensor_maps a (tensor_maps b c))\<close>

definition lvalue :: \<open>('a,'b) maps_hom \<Rightarrow> bool\<close> where

lemma lvalue_hom: "lvalue F \<Longrightarrow> maps_hom F"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom" 
lemma lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom" 
lemma lvalue_mult: "lvalue F \<Longrightarrow> F (comp_domain a b) = comp_domain (F a) (F b)"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom" 

lemma pair_lvalue_axiom: \<open>\<lbrakk>lvalue F; lvalue G; maps_hom p;
    \<And>a b. comp_domain (F a) (G b) = comp_domain (G b) (F a);
    \<And>a b. p (tensor_maps a b) = comp_domain (F a) (G b)\<rbrakk> \<Longrightarrow> lvalue p\<close>


end