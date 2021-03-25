theory Teleport
  imports QHoare
begin


locale teleport_locale = qhoare "TYPE('mem::finite)" +
  fixes X :: "(bit,'mem::finite) maps_hom"
    and \<Phi> :: "(bit*bit,'mem) maps_hom"
    and A :: "('atype::finite,'mem) maps_hom"
    and B :: "('btype::finite,'mem) maps_hom"
  assumes compat[compatible]: "mutually compatible (X,\<Phi>,A,B)"
begin

definition "teleport a b = [
    apply CNOT (pair X (\<Phi> \<circ> Fst)),
    apply hadamard X,
    ifthen (\<Phi> \<circ> Fst) a,
    ifthen X b, 
    apply (if a=1 then pauliX else idOp) (\<Phi> \<circ> Snd),
    apply (if b=1 then pauliZ else idOp) (\<Phi> \<circ> Snd)
  ]"

definition "teleport_pre \<psi> = EQ (pair (pair X A) B) \<psi> \<sqinter> EQ \<Phi> \<beta>00"
definition "teleport_post \<psi> = EQ (pair (pair (\<Phi> o Snd) A) B) \<psi>"


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

definition A :: "(a_state,mem) maps_hom" 
  where \<open>A a = a \<otimes> idOp \<otimes> idOp \<otimes> idOp \<otimes> idOp\<close>

definition X :: "(bit,mem) maps_hom" 
  where \<open>X a = idOp \<otimes> a \<otimes> idOp \<otimes> idOp \<otimes> idOp\<close>

definition \<Phi>1 :: "(bit,mem) maps_hom" 
  where \<open>\<Phi>1 a = idOp \<otimes> idOp \<otimes> a \<otimes> idOp \<otimes> idOp\<close>

definition B :: "(b_state,mem) maps_hom" 
  where \<open>B a = idOp \<otimes> idOp \<otimes> idOp \<otimes> a \<otimes> idOp\<close>

definition \<Phi>2 :: "(bit,mem) maps_hom" 
  where \<open>\<Phi>2 a = idOp \<otimes> idOp \<otimes> idOp \<otimes> idOp \<otimes> a\<close>
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
