theory Teleport
  imports QHoare
    Real_Impl.Real_Impl "HOL-Library.Code_Target_Numeral"
begin

hide_const (open) Finite_Cartesian_Product.vec
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.row
hide_const (open) Finite_Cartesian_Product.column

unbundle no_vec_syntax

lemma [simp]: "dim_vec (vec_of_onb_enum (a :: 'a::enum ell2)) = CARD('a)"
  by (metis canonical_basis_length_ell2_def canonical_basis_length_eq dim_vec_of_onb_enum_list')

(* git cat-file blob 184e3f9d680f199f68d098c03d424db1462ae226:Quantum.thy >bkp.thy *)
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


definition "tensor_state_jnf \<psi> \<phi> = (let d1 = dim_vec \<psi> in let d2 = dim_vec \<phi> in
  vec (d1*d2) (\<lambda>i. let (i1,i2) = tensor_unpack d1 d2 i in (vec_index \<psi> i1) * (vec_index \<phi> i2)))"

lemma tensor_state_jnf_dim[simp]: \<open>dim_vec (tensor_state_jnf \<psi> \<phi>) = dim_vec \<psi> * dim_vec \<phi>\<close>
  unfolding tensor_state_jnf_def Let_def by simp

lemma index_of_nth:
  assumes "distinct xs"
  assumes "i < length xs"
  shows "index_of (xs ! i) xs = i"
  using assms
  by (metis distinct_conv_nth index_of_bound index_of_correct length_nth_simps(1) not_less_zero nth_mem)


lemma enum_idx_enum: 
  assumes \<open>i < CARD('a::enum)\<close>
  shows \<open>enum_idx (enum_class.enum ! i :: 'a) = i\<close>
  unfolding enum_idx_def apply (rule index_of_nth)
  using assms by (simp_all add: card_UNIV_length_enum enum_distinct)

lemma cinner_ket: \<open>\<langle>ket i, \<psi>\<rangle> = Rep_ell2 \<psi> i\<close>
  apply (transfer fixing: i)
  apply (subst infsetsum_cong_neutral[where B=\<open>{i}\<close>])
  by auto

lemma vec_of_onb_enum_ell2_index:
  fixes \<psi> :: \<open>'a::enum ell2\<close> 
  assumes [simp]: \<open>i < CARD('a)\<close>
  shows \<open>vec_of_onb_enum \<psi> $ i = Rep_ell2 \<psi> (Enum.enum ! i)\<close>
proof -
  let ?i = \<open>Enum.enum ! i\<close>
  have \<open>Rep_ell2 \<psi> (Enum.enum ! i) = \<langle>ket ?i, \<psi>\<rangle>\<close>
    by (simp add: cinner_ket)
  also have \<open>\<dots> = vec_of_onb_enum \<psi> \<bullet>c vec_of_onb_enum (ket ?i :: 'a ell2)\<close>
    by (rule cscalar_prod_cinner)
  also have \<open>\<dots> = vec_of_onb_enum \<psi> \<bullet>c unit_vec (CARD('a)) i\<close>
    by (simp add: vec_of_onb_enum_ket enum_idx_enum canonical_basis_length_ell2_def)
  also have \<open>\<dots> = vec_of_onb_enum \<psi> \<bullet> unit_vec (CARD('a)) i\<close>
    by (smt (verit, best) assms carrier_vecI conjugate_conjugate_sprod conjugate_id conjugate_vec_sprod_comm dim_vec_conjugate eq_vecI index_unit_vec(3) scalar_prod_left_unit vec_index_conjugate)
  also have \<open>\<dots> = vec_of_onb_enum \<psi> $ i\<close>
    by simp
  finally show ?thesis
    by simp
qed

lemma enum_prod_nth_tensor_unpack:
  assumes \<open>i < CARD('a) * CARD('b)\<close>
  shows "(Enum.enum ! i :: 'a::enum\<times>'b::enum) = 
        (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in 
              (Enum.enum ! i1, Enum.enum ! i2))"
  using assms 
  by (simp add: enum_prod_def card_UNIV_length_enum product_nth tensor_unpack_def)

lemma vec_of_onb_enum_tensor_state_index:
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('a) * CARD('b)\<close>
  shows \<open>vec_of_onb_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in
    vec_of_onb_enum \<psi> $ i1 * vec_of_onb_enum \<phi> $ i2)\<close>
proof -
  define i1 i2 where "i1 = fst (tensor_unpack CARD('a) CARD('b) i)"
    and "i2 = snd (tensor_unpack CARD('a) CARD('b) i)"
  have [simp]: "i1 < CARD('a)" "i2 < CARD('b)"
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 by presburger

  have \<open>vec_of_onb_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = Rep_ell2 (\<psi> \<otimes>\<^sub>s \<phi>) (enum_class.enum ! i)\<close>
    by (simp add: vec_of_onb_enum_ell2_index)
  also have \<open>\<dots> = Rep_ell2 \<psi> (Enum.enum!i1) * Rep_ell2 \<phi> (Enum.enum!i2)\<close>
    apply (transfer fixing: i i1 i2)
    by (simp add: enum_prod_nth_tensor_unpack case_prod_beta i1_def i2_def)
  also have \<open>\<dots> = vec_of_onb_enum \<psi> $ i1 * vec_of_onb_enum \<phi> $ i2\<close>
    by (simp add: vec_of_onb_enum_ell2_index)
  finally show ?thesis
    by (simp add: case_prod_beta i1_def i2_def)
qed

lemma vec_of_onb_enum_tensor_state:
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  shows \<open>vec_of_onb_enum (\<psi> \<otimes>\<^sub>s \<phi>) = tensor_state_jnf (vec_of_onb_enum \<psi>) (vec_of_onb_enum \<phi>)\<close>
  apply (rule eq_vecI, simp_all)
  apply (subst vec_of_onb_enum_tensor_state_index, simp_all)
  by (simp add: tensor_state_jnf_def case_prod_beta Let_def)

lemma [simp]: \<open>mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2) \<in> carrier_mat CARD('b) CARD('a)\<close>
  by (simp add: canonical_basis_length_ell2_def mat_of_cblinfun_def)
  


lemma mat_of_cblinfun_ell2_index:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> 
  assumes [simp]: \<open>i < CARD('b)\<close> \<open>j < CARD('a)\<close>
  shows \<open>mat_of_cblinfun a $$ (i,j) = Rep_ell2 (a *\<^sub>V ket (Enum.enum ! j)) (Enum.enum ! i)\<close>
proof -
  let ?i = \<open>Enum.enum ! i\<close> and ?j = \<open>Enum.enum ! j\<close> and ?aj = \<open>a *\<^sub>V ket (Enum.enum ! j)\<close>
  have \<open>Rep_ell2 ?aj (Enum.enum ! i) = vec_of_onb_enum ?aj $ i\<close>
    by (rule vec_of_onb_enum_ell2_index[symmetric], simp)
  also have \<open>\<dots> = (mat_of_cblinfun a *\<^sub>v vec_of_onb_enum (ket (enum_class.enum ! j) :: 'a ell2)) $ i\<close>
    by (simp add: mat_of_cblinfun_description)
  also have \<open>\<dots> = (mat_of_cblinfun a *\<^sub>v unit_vec CARD('a) j) $ i\<close>
    by (simp add: vec_of_onb_enum_ket enum_idx_enum canonical_basis_length_ell2_def)
  also have \<open>\<dots> = mat_of_cblinfun a $$ (i, j)\<close>
    apply (subst mat_entry_explicit[where m=\<open>CARD('b)\<close>])
    by auto
  finally show ?thesis
    by auto
qed


lemma dim_row_mat_of_cblinfun[simp]:
  \<open>dim_row (mat_of_cblinfun (a :: 'a::onb_enum\<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum)) = canonical_basis_length TYPE('b)\<close>
  unfolding mat_of_cblinfun_def by auto

lemma dim_col_mat_of_cblinfun[simp]:
  \<open>dim_col (mat_of_cblinfun (a :: 'a::onb_enum\<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum)) = canonical_basis_length TYPE('a)\<close>
  unfolding mat_of_cblinfun_def by auto

lemma mat_of_cblinfun_tensor_op_index:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> and b :: \<open>'c::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('b) * CARD('d)\<close>
  assumes [simp]: \<open>j < CARD('a) * CARD('c)\<close>
  shows \<open>mat_of_cblinfun (tensor_op a b) $$ (i,j) = 
            (let (i1,i2) = tensor_unpack CARD('b) CARD('d) i in
             let (j1,j2) = tensor_unpack CARD('a) CARD('c) j in
                  mat_of_cblinfun a $$ (i1,j1) * mat_of_cblinfun b $$ (i2,j2))\<close>
proof -
  define i1 i2 j1 j2
    where "i1 = fst (tensor_unpack CARD('b) CARD('d) i)"
      and "i2 = snd (tensor_unpack CARD('b) CARD('d) i)"
      and "j1 = fst (tensor_unpack CARD('a) CARD('c) j)"
      and "j2 = snd (tensor_unpack CARD('a) CARD('c) j)"
  have [simp]: "i1 < CARD('b)" "i2 < CARD('d)" "j1 < CARD('a)" "j2 < CARD('c)"
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 apply blast
    using assms(2) j1_def tensor_unpack_bound1 apply blast
    using assms(2) j2_def tensor_unpack_bound2 by presburger

  have \<open>mat_of_cblinfun (tensor_op a b) $$ (i,j) 
       = Rep_ell2 (tensor_op a b *\<^sub>V ket (Enum.enum!j)) (Enum.enum ! i)\<close>
    by (simp add: mat_of_cblinfun_ell2_index)
  also have \<open>\<dots> = Rep_ell2 ((a *\<^sub>V ket (Enum.enum!j1)) \<otimes>\<^sub>s (b *\<^sub>V ket (Enum.enum!j2))) (Enum.enum!i)\<close>
    by (simp add: tensor_op_ell2 enum_prod_nth_tensor_unpack[where i=j] Let_def case_prod_beta j1_def[symmetric] j2_def[symmetric] flip: tensor_ell2_ket)
  also have \<open>\<dots> = vec_of_onb_enum ((a *\<^sub>V ket (Enum.enum!j1)) \<otimes>\<^sub>s b *\<^sub>V ket (Enum.enum!j2)) $ i\<close>
    by (simp add: vec_of_onb_enum_ell2_index)
  also have \<open>\<dots> = vec_of_onb_enum (a *\<^sub>V ket (enum_class.enum ! j1)) $ i1 *
                  vec_of_onb_enum (b *\<^sub>V ket (enum_class.enum ! j2)) $ i2\<close>
    by (simp add: case_prod_beta vec_of_onb_enum_tensor_state_index i1_def[symmetric] i2_def[symmetric])
  also have \<open>\<dots> = Rep_ell2 (a *\<^sub>V ket (enum_class.enum ! j1)) (enum_class.enum ! i1) *
                  Rep_ell2 (b *\<^sub>V ket (enum_class.enum ! j2)) (enum_class.enum ! i2)\<close>
    by (simp add: vec_of_onb_enum_ell2_index)
  also have \<open>\<dots> = mat_of_cblinfun a $$ (i1, j1) * mat_of_cblinfun b $$ (i2, j2)\<close>
    by (simp add: mat_of_cblinfun_ell2_index)
  finally show ?thesis
    by (simp add: i1_def[symmetric] i2_def[symmetric] j1_def[symmetric] j2_def[symmetric] case_prod_beta)
qed


definition "tensor_op_jnf A B = 
  (let r1 = dim_row A in
   let c1 = dim_col A in
   let r2 = dim_row B in
   let c2 = dim_col B in
   mat (r1*r2) (c1*c2)
   (\<lambda>(i,j). let (i1,i2) = tensor_unpack r1 r2 i in
            let (j1,j2) = tensor_unpack c1 c2 j in
              (A $$ (i1,j1)) * (B $$ (i2,j2))))"

lemma tensor_op_jnf_dim[simp]: 
  \<open>dim_row (tensor_op_jnf a b) = dim_row a * dim_row b\<close>
  \<open>dim_col (tensor_op_jnf a b) = dim_col a * dim_col b\<close>
  unfolding tensor_op_jnf_def Let_def by simp_all


lemma mat_of_cblinfun_tensor_op:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> and b :: \<open>'c::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::enum ell2\<close>
  shows \<open>mat_of_cblinfun (tensor_op a b) = tensor_op_jnf (mat_of_cblinfun a) (mat_of_cblinfun b)\<close>
  apply (rule eq_matI, simp_all add: canonical_basis_length_ell2_def)
  apply (subst mat_of_cblinfun_tensor_op_index, simp_all)
  by (simp add: tensor_op_jnf_def case_prod_beta Let_def canonical_basis_length_ell2_def)

locale teleport_locale = qhoare "TYPE('mem::finite)" +
  fixes X :: "(bit,'mem::finite) maps_hom"
    and \<Phi> :: "(bit*bit,'mem) maps_hom"
    and A :: "('atype::finite,'mem) maps_hom"
    and B :: "('btype::finite,'mem) maps_hom"
  assumes compat[compatible]: "mutually compatible (X,\<Phi>,A,B)"
begin

abbreviation "\<Phi>1 \<equiv> \<Phi> \<circ> Fst"
abbreviation "\<Phi>2 \<equiv> \<Phi> \<circ> Snd"
abbreviation "X\<Phi>2 \<equiv> pair X \<Phi>2"
abbreviation "X\<Phi>1 \<equiv> pair X \<Phi>1"
abbreviation "X\<Phi> \<equiv> pair X \<Phi>"

definition "teleport a b = [
    apply CNOT X\<Phi>1,
    apply hadamard X,
    ifthen \<Phi>1 a,
    ifthen X b, 
    apply (if a=1 then pauliX else idOp) \<Phi>2,
    apply (if b=1 then pauliZ else idOp) \<Phi>2
  ]"

definition "teleport_pre \<psi> = EQ (pair (pair X A) B) \<psi> \<sqinter> EQ \<Phi> \<beta>00"
definition "teleport_post \<psi> = EQ (pair (pair (\<Phi> o Snd) A) B) \<psi>"

lemma swap_sandwich: "swap a = Uswap o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Uswap"
  sorry


lemma mat_of_cblinfun_assoc_ell2'[simp]: 
  \<open>mat_of_cblinfun (assoc_ell2' :: (('a::enum\<times>'b::enum\<times>'c::enum) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = one_mat (CARD('a)*CARD('b)*CARD('c))\<close>
  sorry

lemma [simp]: "dim_col (mat_adjoint m) = dim_row m"
  sorry
lemma [simp]: "dim_row (mat_adjoint m) = dim_col m"
  sorry

term tensor_maps_hom
lemma tensor_maps_hom_sandwich2: "id \<otimes>\<^sub>h (\<lambda>a. b o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L c) = (\<lambda>a. (tensor_op idOp b) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L (tensor_op idOp c))"
  sorry

lemma tmp1: \<open>\<Phi> a = X\<Phi> (idOp \<otimes> a)\<close>
  by auto
lemma tmp2: \<open>X\<Phi>1 a = X\<Phi> (assoc (a \<otimes> idOp))\<close>
  by -
lemma tmp3: \<open>X\<Phi>2 a = X\<Phi> ((id \<otimes>\<^sub>h swap) (assoc (a \<otimes> idOp)))\<close>
  by -
lemma tmp4: 
  assumes "mat_of_cblinfun a = mat_of_cblinfun b"
  shows "a = b"
  by (metis assms mat_of_cblinfun_inverse)
lemma tmp5: "mat_of_cblinfun (assoc_ell2:: (('a::enum \<times> 'b::enum) \<times> 'c::enum) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b \<times> 'c) ell2)
           = one_mat (CARD('a)*CARD('b)*CARD('c))"
  by -
lemma tmp6: "r *\<^sub>R X\<Phi> a = X\<Phi> (r *\<^sub>R a)"
  sorry
lemma card_bit[simp]: "CARD(bit) = 2"
  using card_2_iff' by force
definition [code del]: "EQQ x y \<longleftrightarrow> undefined"
lemma XXX: "EQQ (col M 0) (col N 0) \<Longrightarrow> False \<Longrightarrow> M=N"
  by simp
(* Trying things out *)
definition T where \<open>T = butterfly (ket 1 \<otimes>\<^sub>s \<beta>00) (ket (0,0,0))\<close>
lemma "X\<Phi>1 (butterfly (ket (0,0)) \<beta>00) o\<^sub>C\<^sub>L \<Phi> (selfbutter \<beta>00) =
       (1/2) *\<^sub>R X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ket 0 \<otimes>\<^sub>s ket 0) \<beta>00)"
  apply (simp only: tmp1 tmp2 tmp3 tmp6)
  apply (simp add: lvalue_mult[of X\<Phi>] del: pair_apply)
  apply (rule arg_cong[of _ _ X\<Phi>])
  apply (rule tmp4)
  apply (simp add: assoc_def tmp5 mat_of_cblinfun_tensor_op
butterfly_def' cblinfun_of_mat_timesOp mat_of_cblinfun_ell2_to_l2bounded
canonical_basis_length_ell2_def mat_of_cblinfun_adjoint' vec_of_onb_enum_ket
cblinfun_of_mat_id swap_sandwich[abs_def]  mat_of_cblinfun_scaleR mat_of_cblinfun_scalarMult
tensor_maps_hom_sandwich2 vec_of_onb_enum_tensor_state
T_def)
  (* using XXX *)
  (* apply (rule XXX) *)
  (* apply eval *)
  by normalization


lemma teleport: "hoare (teleport_pre \<psi>) (teleport a b) (teleport_post \<psi>)" for \<psi> a b
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
    apply (subst swap_EQP', simp)
    apply (subst join_EQP', simp)
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
    by (metis (no_types, lifting) compat compatible_lvalue2 pair_apply lvalue_def times_idOp2)
  have join2: \<open>(pair (\<Phi> \<circ> Fst) X) M = (pair X \<Phi>) ((id \<otimes>\<^sub>h Fst) (swap M))\<close> for M
    apply (subst pair_comp_tensor')
       apply simp_all[3]
    apply (subst pair_comp_swap', simp)
    by simp
  have join3: "X M = (pair X \<Phi>) (M \<otimes> idOp)" for M
    by force
  have join4: \<open>(pair X (\<Phi> \<circ> Fst)) M = (pair X \<Phi>) ((id \<otimes>\<^sub>h Fst) M)\<close> for M
    apply (subst pair_comp_tensor')
    by simp_all

  have "O7 = xxx"
    unfolding O7_def O5_def' O3_def O2_def O1_def
    apply (simp only: join1 join2 join3 join4 EQP_def)
    apply simp
    sorry
  show ?thesis
    sorry
qed

end


locale concrete_teleport_vars begin

type_synonym a_state = "64 word"
type_synonym b_state = "1000000 word"
type_synonym mem = "a_state * bit * bit * b_state * bit"
type_synonym 'a var = \<open>('a,mem) maps_hom\<close>

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
