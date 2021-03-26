theory Teleport
  imports QHoare
begin

hide_const (open) Finite_Cartesian_Product.vec
hide_type (open) Finite_Cartesian_Product.vec

lemma [simp]: "dim_vec (vec_of_onb_enum (a :: 'a::enum ell2)) = CARD('a)"
  by (metis canonical_basis_length_ell2_def canonical_basis_length_eq dim_vec_of_onb_enum_list')

(* git cat-file blob 184e3f9d680f199f68d098c03d424db1462ae226:Quantum.thy >bkp.thy *)
definition tensor_pack :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat" where "tensor_pack X Y = (\<lambda>(x, y). x * Y + y)"
definition tensor_unpack :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"  where "tensor_unpack X Y xy = (xy div Y, xy mod Y)"

definition "tensor_state_jnf \<psi> \<phi> = (let d1 = dim_vec \<psi> in let d2 = dim_vec \<phi> in
  vec (d1*d2) (\<lambda>i. let (i1,i2) = tensor_unpack d1 d2 i in (vec_index \<psi> i1) * (vec_index \<phi> i2)))"

lemma tensor_state_jnf_dim[simp]: \<open>dim_vec (tensor_state_jnf \<psi> \<phi>) = dim_vec \<psi> * dim_vec \<phi>\<close>
  unfolding tensor_state_jnf_def Let_def by simp

lemma
  fixes \<psi> :: \<open>'a::enum ell2\<close> 
  assumes \<open>i < CARD('a)\<close>
  shows \<open>vec_of_onb_enum \<psi> $ i = Rep_ell2 \<psi> (Enum.enum ! i)\<close>
  unfolding vec_of_onb_enum_def apply simp
  apply (subst index_map_vec)
  apply simp
   apply (metis assms canonical_basis_length_ell2_def canonical_basis_length_eq)
  unfolding canonical_basis_ell2_def
  apply simp
  by
simp

lemma 
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  shows \<open>vec_of_onb_enum (\<psi> \<otimes>\<^sub>s \<phi>) $ i = (let (i1,i2) = tensor_unpack CARD('a) CARD('b) i in
    vec_of_onb_enum \<psi> $ i1 * vec_of_onb_enum \<phi> $ i2)\<close>


lemma 
  fixes \<psi> :: \<open>'a::enum ell2\<close> and \<phi> :: \<open>'b::enum ell2\<close>
  shows \<open>vec_of_onb_enum (\<psi> \<otimes>\<^sub>s \<phi>) = tensor_state_jnf (vec_of_onb_enum \<psi>) (vec_of_onb_enum \<phi>)\<close>
proof (rule eq_vecI, simp_all)
  fix i
  assume \<open>i < CARD('a) * CARD('b)\<close>
  
  by simp

lift_definition tensor_op :: \<open>('a::enum, 'b::enum) operator \<Rightarrow> ('c::enum, 'd::enum) operator 
                                 \<Rightarrow> ('a\<times>'c, 'b\<times>'d) operator\<close> is
  \<open>\<lambda>A B. mat (CARD('b)*CARD('d)) (CARD('a)*CARD('c)) 
      (\<lambda>(i,j). let (i1,i2) = tensor_unpack CARD('b) CARD('d) i in
               let (j1,j2) = tensor_unpack CARD('a) CARD('c) j in
               A $$ (i1, j1) * B $$ (i2, j2))\<close>
  by auto



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
lemma card_bit[simp]: "CARD(bit) = 2"
  using card_2_iff' by force
(* Trying things out *)
lemma "X\<Phi>1 (butterfly (ket (0,0)) \<beta>00) o\<^sub>C\<^sub>L \<Phi> (selfbutter \<beta>00) = 
       X\<Phi>2 Uswap o\<^sub>C\<^sub>L \<Phi> (butterfly (ketplus \<otimes>\<^sub>s ket 0) \<beta>00)"
  apply (simp only: tmp1 tmp2 tmp3)
  (* using[[simp_trace_new]] *)
  apply (simp add: lvalue_mult[of X\<Phi>] del: pair_apply)
  apply (rule arg_cong[of _ _ X\<Phi>])
  apply (rule tmp4)
  apply (simp add: assoc_def cblinfun_of_mat_timesOp tmp5)
  

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
