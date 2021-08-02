theory Pure_States
  imports Laws_Complement_Quantum "HOL-Eisbach.Eisbach"
begin

instance complement_domain :: (type, type) default..

definition \<open>pure_state_target_vector F \<eta>\<^sub>F = (if ket default \<in> range (cblinfun_apply (F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F)))
   then ket default
   else (SOME \<eta>'. norm \<eta>' = 1 \<and> \<eta>' \<in> range (cblinfun_apply (F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F)))))\<close>

lemma pure_state_target_vector_eqI:
  assumes \<open>F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F) = G (butterfly \<eta>\<^sub>G \<eta>\<^sub>G)\<close>
  shows \<open>pure_state_target_vector F \<eta>\<^sub>F = pure_state_target_vector G \<eta>\<^sub>G\<close>
  by (simp add: assms pure_state_target_vector_def)

lemma pure_state_target_vector_ket_default: \<open>pure_state_target_vector F \<eta>\<^sub>F = ket default\<close> if \<open>ket default \<in> range (cblinfun_apply (F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F)))\<close>
  by (simp add: pure_state_target_vector_def that)

lemma
  assumes [simp]: \<open>\<eta>\<^sub>F \<noteq> 0\<close> \<open>register F\<close>
  shows pure_state_target_vector_in_range: \<open>pure_state_target_vector F \<eta>\<^sub>F \<in> range ((*\<^sub>V) (F (selfbutter \<eta>\<^sub>F)))\<close> (is ?range)
    and pure_state_target_vector_norm: \<open>norm (pure_state_target_vector F \<eta>\<^sub>F) = 1\<close> (is ?norm)
proof -
  from assms have \<open>selfbutter \<eta>\<^sub>F \<noteq> 0\<close>
    by (metis butterfly_0_right complex_vector.scale_zero_right inj_selfbutter_upto_phase)
  then have \<open>F (selfbutter \<eta>\<^sub>F) \<noteq> 0\<close>
    using register_inj[OF \<open>register F\<close>, THEN injD, where y=0]
    by (auto simp: complex_vector.linear_0)
  then obtain \<psi>' where \<psi>': \<open>F (selfbutter \<eta>\<^sub>F) *\<^sub>V \<psi>' \<noteq> 0\<close>
    by (meson cblinfun_eq_0_on_UNIV_span complex_vector.span_UNIV)
  have ex: \<open>\<exists>\<psi>. norm \<psi> = 1 \<and> \<psi> \<in> range ((*\<^sub>V) (F (selfbutter \<eta>\<^sub>F)))\<close>
    apply (rule exI[of _ \<open>(F (selfbutter \<eta>\<^sub>F) *\<^sub>V \<psi>') /\<^sub>C norm (F (selfbutter \<eta>\<^sub>F) *\<^sub>V \<psi>')\<close>])
    using \<psi>' apply (auto simp add: norm_inverse)
    by (metis cblinfun.scaleC_right rangeI)
  then show ?range
    by (metis (mono_tags, lifting) pure_state_target_vector_def verit_sko_ex')
  show ?norm
    apply (simp add: pure_state_target_vector_def)
    using ex by (metis (mono_tags, lifting) verit_sko_ex')
qed


lemma pure_state_target_vector_correct: 
  assumes [simp]: \<open>\<eta> \<noteq> 0\<close> \<open>register F\<close>
  shows \<open>F (selfbutter \<eta>) *\<^sub>V pure_state_target_vector F \<eta> \<noteq> 0\<close>
proof -
  obtain \<psi> where \<psi>: \<open>F (selfbutter \<eta>) \<psi> = pure_state_target_vector F \<eta>\<close>
    apply atomize_elim
    using pure_state_target_vector_in_range[OF assms]
    by (smt (verit, best) image_iff top_ccsubspace.rep_eq top_set_def)

  define n where \<open>n = cinner \<eta> \<eta>\<close>
  then have \<open>n \<noteq> 0\<close>
    by auto

  have pure_state_target_vector_neq0: \<open>pure_state_target_vector F \<eta> \<noteq> 0\<close>
    using pure_state_target_vector_norm[OF assms]
    by auto

  have \<open>F (selfbutter \<eta>) *\<^sub>V pure_state_target_vector F \<eta> = F (selfbutter \<eta>) *\<^sub>V F (selfbutter \<eta>) *\<^sub>V \<psi>\<close>
    by (simp add: \<psi>)
  also have \<open>\<dots> = n *\<^sub>C F (selfbutter \<eta>) *\<^sub>V \<psi>\<close>
    by (simp flip: cblinfun_apply_cblinfun_compose add: register_mult register_scaleC n_def)
  also have \<open>\<dots> = n *\<^sub>C pure_state_target_vector F \<eta>\<close>
    by (simp add: \<psi>)
  also have \<open>\<dots> \<noteq> 0\<close>
    using pure_state_target_vector_neq0 \<open>n \<noteq> 0\<close>
    by auto
  finally show ?thesis
    by -
qed

definition \<open>pure_state' F \<psi> \<eta>\<^sub>F = F (butterfly \<psi> \<eta>\<^sub>F) *\<^sub>V pure_state_target_vector F \<eta>\<^sub>F\<close>

abbreviation \<open>pure_state F \<psi> \<equiv> pure_state' F \<psi> (ket default)\<close>

nonterminal pure_tensor
syntax "_pure_tensor" :: \<open>'a \<Rightarrow> 'b \<Rightarrow> pure_tensor \<Rightarrow> pure_tensor\<close> ("_ _ \<otimes>\<^sub>p _" [1000, 0, 0] 1000)
syntax "_pure_tensor2" :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> pure_tensor\<close> ("_ _ \<otimes>\<^sub>p _ _" [1000, 0, 1000, 0] 1000)
syntax "_pure_tensor1" :: \<open>'a \<Rightarrow> 'b \<Rightarrow> pure_tensor\<close>
syntax "_pure_tensor_start" :: \<open>pure_tensor \<Rightarrow> 'a\<close> ("'(_')")

translations
  "_pure_tensor2 F \<psi> G \<phi>" \<rightharpoonup> "CONST pure_state (F; G) (\<psi> \<otimes>\<^sub>s \<phi>)"
  "_pure_tensor F \<psi> (CONST pure_state G \<phi>)" \<rightharpoonup> "CONST pure_state (F; G) (\<psi> \<otimes>\<^sub>s \<phi>)"
  "_pure_tensor_start x" \<rightharpoonup> "x"

  "_pure_tensor_start (_pure_tensor2 F \<psi> G \<phi>)" \<leftharpoondown> "CONST pure_state (F; G) (\<psi> \<otimes>\<^sub>s \<phi>)"
  "_pure_tensor F \<psi> (_pure_tensor2 G \<phi> H \<eta>)" \<leftharpoondown> "_pure_tensor2 F \<psi> (G;H) (\<phi> \<otimes>\<^sub>s \<eta>)"

term \<open>(F \<psi> \<otimes>\<^sub>p G \<phi> \<otimes>\<^sub>p H z)\<close>
term \<open>pure_state (F; G) (a \<otimes>\<^sub>s b)\<close>

lemma register_pair_butterfly_tensor: \<open>(F; G) (butterfly (a \<otimes>\<^sub>s b) (c \<otimes>\<^sub>s d)) = F (butterfly a c) o\<^sub>C\<^sub>L G (butterfly b d)\<close>
  if [simp]: \<open>compatible F G\<close>
  by (auto simp: default_prod_def simp flip: tensor_ell2_ket tensor_butterfly register_pair_apply)

(* lemma aux3: \<open>(F; G) (butterfly (a \<otimes>\<^sub>s b) (ket default)) = F (butterfly a (ket default)) o\<^sub>C\<^sub>L G (butterfly b (ket default))\<close>
  if [simp]: \<open>compatible F G\<close>
  by (auto simp: default_prod_def simp flip: tensor_ell2_ket tensor_butterfly register_pair_apply) *)

(* lemma aux4: \<open>(F; G) (butterfly (ket default) (a \<otimes>\<^sub>s b)) = F (butterfly (ket default) a) o\<^sub>C\<^sub>L G (butterfly (ket default) b)\<close>
  if [simp]: \<open>compatible F G\<close>
  by (auto simp: default_prod_def simp flip: tensor_ell2_ket tensor_butterfly register_pair_apply) *)

(* lemma aux1: \<open>(F; G) (selfbutterket default) = F (selfbutterket default) o\<^sub>C\<^sub>L G (selfbutterket default)\<close>
  if [simp]: \<open>compatible F G\<close>
  by (auto simp: default_prod_def simp flip: tensor_ell2_ket tensor_butterfly register_pair_apply) *)

lemma pure_state_eqI:
  assumes \<open>F (selfbutter \<eta>\<^sub>F) = G (selfbutter \<eta>\<^sub>G)\<close>
  assumes \<open>F (butterfly \<psi> \<eta>\<^sub>F) = G (butterfly \<phi> \<eta>\<^sub>G)\<close>
  shows \<open>pure_state' F \<psi> \<eta>\<^sub>F = pure_state' G \<phi> \<eta>\<^sub>G\<close>
proof -
  from assms(1) have \<open>pure_state_target_vector F \<eta>\<^sub>F = pure_state_target_vector G \<eta>\<^sub>G\<close>
    by (rule pure_state_target_vector_eqI)
  with assms(2)
  show ?thesis
    unfolding pure_state'_def
    by simp
qed


(* (* Example *)
lemma example1: \<open>(F f \<otimes>\<^sub>p G g \<otimes>\<^sub>p H h) = (H h \<otimes>\<^sub>p G g \<otimes>\<^sub>p F f)\<close>
  (is \<open>pure_state ?FGH ?fgh = pure_state ?HGF ?hgf\<close>)
  if [simp]: \<open>mutually compatible (F, G, H)\<close> \<open>register F\<close> \<open>register G\<close> \<open>register H\<close>
  apply (rule pure_state_eqI)
  by (auto simp: register_pair_butterfly_tensor compatible_ac_rules default_prod_def simp flip: tensor_ell2_ket)

(* Example *)
lemma example2: \<open>pure_state (F;(G;H)) (f \<otimes>\<^sub>s g \<otimes>\<^sub>s h) = pure_state ((F;G);H) ((f \<otimes>\<^sub>s g) \<otimes>\<^sub>s h)\<close>
  if [compatible]: \<open>mutually compatible (F, G, H)\<close>
  apply (rule pure_state_eqI)
  by (auto simp: register_pair_butterfly_tensor compatible_ac_rules default_prod_def simp flip: tensor_ell2_ket) *)

definition \<open>regular_register F \<longleftrightarrow> register F \<and> (\<exists>a. (F; complement F) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default)\<close>


(* TODO: rewrite without using registers, move to Finite_Tensor_Product *)
lemma overlapping_tensor:
  assumes eq: \<open>butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = assoc (b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>')\<close>
  assumes \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close>
  shows \<open>\<exists>c. butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
proof -
  note id_cblinfun_eq_1[simp del]
  define d where \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>
  
  define \<psi>\<^sub>n \<psi>\<^sub>n' a23\<^sub>n where \<open>\<psi>\<^sub>n = \<psi> /\<^sub>C norm \<psi>\<close> and \<open>\<psi>\<^sub>n' = \<psi>' /\<^sub>C norm \<psi>'\<close> and \<open>a23\<^sub>n = norm \<psi> *\<^sub>C norm \<psi>' *\<^sub>C a23\<close>
  have [simp]: \<open>norm \<psi>\<^sub>n = 1\<close> \<open>norm \<psi>\<^sub>n' = 1\<close>
    using \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> by (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def norm_inverse)
  have n1: \<open>butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o a23\<^sub>n = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>
    apply (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def a23\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(2) assms(3) inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_eq_0_iff right_inverse scaleC_one)

  define \<phi>\<^sub>n \<phi>\<^sub>n' b12\<^sub>n where \<open>\<phi>\<^sub>n = \<phi> /\<^sub>C norm \<phi>\<close> and \<open>\<phi>\<^sub>n' = \<phi>' /\<^sub>C norm \<phi>'\<close> and \<open>b12\<^sub>n = norm \<phi> *\<^sub>C norm \<phi>' *\<^sub>C b12\<close>
  have [simp]: \<open>norm \<phi>\<^sub>n = 1\<close> \<open>norm \<phi>\<^sub>n' = 1\<close>
    using \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close> by (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def norm_inverse)
  have n2: \<open>b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n' = b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    apply (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def b12\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(4) assms(5) field_class.field_inverse inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_hom.hom_0 scaleC_one)

  define c' :: \<open>(unit*'b*unit) ell2 \<Rightarrow>\<^sub>C\<^sub>L (unit*'b*unit) ell2\<close> 
    where \<open>c' = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)* o\<^sub>C\<^sub>L d
            o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')\<close>

  define c'' :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where \<open>c'' = (empty_var;(id;empty_var)) c'\<close>

  have c'_c'': \<open>c' = id_cblinfun \<otimes>\<^sub>o c'' \<otimes>\<^sub>o id_cblinfun\<close>
    unfolding c''_def
    apply (rule fun_cong[where x=c'])
    apply (rule tensor_extensionality3)
      apply auto[2]
    apply (auto simp: register_pair_apply)
    apply (auto simp: empty_var_def)
    by (metis (no_types, lifting) id_cblinfun_eq_1 one_dim_scaleC_1 scaleC_scaleC tensor_op_scaleC_left tensor_op_scaleC_right)

  define c :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where \<open>c = c'' /\<^sub>C norm \<psi> /\<^sub>C norm \<psi>' /\<^sub>C norm \<phi> /\<^sub>C norm \<phi>'\<close>

  have \<open>d = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n1[symmetric] comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n')
                  o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def eq n2 assoc_ell2_sandwich cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n') o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
              o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc
              ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (assoc' d) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
              o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n2 eq)
  also have \<open>\<dots> = ((butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (assoc (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n)))
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (assoc (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n') o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: assoc_ell2_sandwich assoc_ell2'_sandwich sandwich_def cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n')\<close>
    apply (simp only: tensor_id[symmetric] assoc_apply comp_tensor_op)
    by (simp add: cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L c' o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')*\<close>
    apply (simp add: c'_def butterfly_def_one_dim[where 'c="unit ell2"] cblinfun_assoc_left comp_tensor_op
                      tensor_op_adjoint cnorm_eq_1[THEN iffD1])
    by (simp add: cblinfun_assoc_right comp_tensor_op)
  also have \<open>\<dots> = butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o c'' \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n'\<close>
    by (simp add: c'_c'' comp_tensor_op tensor_op_adjoint butterfly_def_one_dim[symmetric])
  also have \<open>\<dots> = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by (simp add: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def \<phi>\<^sub>n_def \<phi>\<^sub>n'_def c_def tensor_op_scaleC_left tensor_op_scaleC_right)
  finally have d_c: \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by -
  then show ?thesis
    by (auto simp: d_def)
qed

lemma regular_register_pair:
  assumes [simp]: \<open>compatible F G\<close>
  assumes \<open>regular_register F\<close> and \<open>regular_register G\<close>
  shows \<open>regular_register (F;G)\<close>
proof -
  have [simp]: \<open>bij (F;complement F)\<close> \<open>bij (G;complement G)\<close>
    using assms(1) compatible_def complement_is_complement complements_def iso_register_bij by blast+
  have [simp]: \<open>bij ((F;G);complement (F;G))\<close>
    using assms(1) complement_is_complement complements_def iso_register_bij pair_is_register by blast
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms(1) unfolding compatible_def by auto
  
  obtain aF where [simp]: \<open>inv (F;complement F) (selfbutterket default) = selfbutterket default \<otimes>\<^sub>o aF\<close>
    by (metis assms(2) compatible_complement_right invI pair_is_register register_inj regular_register_def)
  obtain aG where [simp]: \<open>inv (G;complement G) (selfbutterket default) = selfbutterket default \<otimes>\<^sub>o aG\<close>
    by (metis assms(3) complement_is_complement complements_def inj_iff inv_f_f iso_register_inv_comp1 regular_register_def)
  define t1 where \<open>t1 = inv ((F;G); complement (F;G)) (selfbutterket default)\<close>
  define t2 where \<open>t2 = inv (F; (G; complement (F;G))) (selfbutterket default)\<close>
  define t3 where \<open>t3 = inv (G; (F; complement (F;G))) (selfbutterket default)\<close>


  have \<open>complements F (G; complement (F;G))\<close>
    apply (rule complements_complement_pair)
    by simp
  then have \<open>equivalent_registers (complement F) (G; complement (F;G))\<close>
    using Laws_Complement_Quantum.complement_unique equivalent_registers_sym by blast
  then obtain I where [simp]: \<open>iso_register I\<close> and I: \<open>(G; complement (F;G)) = complement F o I\<close>
    by (metis equivalent_registers_def)
  then have [simp]: \<open>register I\<close>
    by (meson iso_register_is_register)
  have [simp]: \<open>bij (id \<otimes>\<^sub>r I)\<close>
    by (rule iso_register_bij, simp)
  have [simp]: \<open>inv (id \<otimes>\<^sub>r I) = id \<otimes>\<^sub>r inv I\<close>
    by auto

  have \<open>t2 = (inv (id \<otimes>\<^sub>r I) o inv (F;complement F)) (selfbutterket default)\<close>
    unfolding t2_def I
    apply (subst o_inv_distrib[symmetric]) 
    by (auto simp: pair_o_tensor)
  also have \<open>\<dots> = (selfbutterket default \<otimes>\<^sub>o inv I aF)\<close>
    apply auto
    by (metis \<open>iso_register I\<close> id_def iso_register_def iso_register_inv register_id register_tensor_apply)
  finally have t2': \<open>t2 = selfbutterket default \<otimes>\<^sub>o inv I aF\<close>
    by simp

  have *: \<open>complements G (F; complement (F;G))\<close>
    apply (rule complements_complement_pair')
    by simp
  then have [simp]: \<open>compatible G (F; complement (F;G))\<close>
    using complements_def by blast
  from * have \<open>equivalent_registers (complement G) (F; complement (F;G))\<close>
    using complement_unique equivalent_registers_sym by blast
  then obtain J where [simp]: \<open>iso_register J\<close> and I: \<open>(F; complement (F;G)) = complement G o J\<close>
    by (metis equivalent_registers_def)
  then have [simp]: \<open>register J\<close>
    by (meson iso_register_is_register)
  have [simp]: \<open>bij (id \<otimes>\<^sub>r J)\<close>
    by (rule iso_register_bij, simp)
  have [simp]: \<open>inv (id \<otimes>\<^sub>r J) = id \<otimes>\<^sub>r inv J\<close>
    by auto

  have \<open>t3 = (inv (id \<otimes>\<^sub>r J) o inv (G;complement G)) (selfbutterket default)\<close>
    unfolding t3_def I
    apply (subst o_inv_distrib[symmetric]) 
    by (auto simp: pair_o_tensor)
  also have \<open>\<dots> = (selfbutterket default \<otimes>\<^sub>o inv J aG)\<close>
    apply auto
    by (metis \<open>iso_register J\<close> id_def iso_register_def iso_register_inv register_id register_tensor_apply)
  finally have t3': \<open>t3 = selfbutterket default \<otimes>\<^sub>o inv J aG\<close>
    by simp

  have *: \<open>((F;G); complement (F;G)) o assoc' = (F; (G; complement (F;G)))\<close>
    apply (rule tensor_extensionality3)
    by (auto simp: register_pair_apply  compatible_complement_pair1 compatible_complement_pair2)
  have t2_t1: \<open>t2 = assoc t1\<close>
    unfolding t1_def t2_def *[symmetric] apply (subst o_inv_distrib)
    by auto

  have *: \<open>((F;G); complement (F;G)) o (swap \<otimes>\<^sub>r id) o assoc' = (G; (F; complement (F;G)))\<close>
    apply (rule tensor_extensionality3)
      apply (auto intro!: register_comp register_tensor_is_hom pair_is_register complements_complement_pair
        simp: register_pair_apply compatible_complement_pair1)
    by (metis assms(1) cblinfun_assoc_left(1) swap_registers_left)
  have t3_t1: \<open>t3 = assoc ((swap \<otimes>\<^sub>r id) t1)\<close>
    unfolding t1_def t3_def *[symmetric] apply (subst o_inv_distrib)
    by (auto intro!: bij_comp simp: iso_register_bij o_inv_distrib)

  from \<open>t2 = assoc t1\<close> \<open>t3 = assoc ((swap \<otimes>\<^sub>r id) t1)\<close>
  have *: \<open>selfbutterket default \<otimes>\<^sub>o inv J aG =  assoc ((swap \<otimes>\<^sub>r id) (assoc' (selfbutterket default \<otimes>\<^sub>o inv I aF)))\<close>
    by (simp add: t2' t3')

  have \<open>selfbutterket default \<otimes>\<^sub>o swap (inv J aG) = (id \<otimes>\<^sub>r swap) (selfbutterket default \<otimes>\<^sub>o inv J aG)\<close>
    by auto
  also have \<open>\<dots> = ((id \<otimes>\<^sub>r swap) o assoc o (swap \<otimes>\<^sub>r id) o assoc') (selfbutterket default \<otimes>\<^sub>o inv I aF)\<close>
    by (simp add: *)
  also have \<open>\<dots> = (assoc o swap) (selfbutterket default \<otimes>\<^sub>o inv I aF)\<close>
    apply (rule fun_cong[where g=\<open>assoc o swap\<close>])
    apply (intro tensor_extensionality3 register_comp register_tensor_is_hom)
    by auto
  also have \<open>\<dots> = assoc (inv I aF \<otimes>\<^sub>o selfbutterket default)\<close>
    by auto
  finally have *: \<open>selfbutterket default \<otimes>\<^sub>o swap (inv J aG) = assoc (inv I aF \<otimes>\<^sub>o selfbutterket default)\<close>
    by -

  obtain c where *: \<open>selfbutterket (default::'c) \<otimes>\<^sub>o swap (inv J aG) = selfbutterket default \<otimes>\<^sub>o c \<otimes>\<^sub>o selfbutterket default\<close>
    apply atomize_elim
    using * apply (rule overlapping_tensor)
    by auto

  have \<open>t1 = ((swap \<otimes>\<^sub>r id) o assoc') t3\<close>
    by (simp add: t3_t1 register_tensor_distrib[unfolded o_def, THEN fun_cong] flip: id_def)
  also have \<open>\<dots> = ((swap \<otimes>\<^sub>r id) o assoc' o (id \<otimes>\<^sub>r swap)) (selfbutterket (default::'c) \<otimes>\<^sub>o swap (inv J aG))\<close>
    unfolding t3' by auto
  also have \<open>\<dots> = ((swap \<otimes>\<^sub>r id) o assoc' o (id \<otimes>\<^sub>r swap)) (selfbutterket default \<otimes>\<^sub>o c \<otimes>\<^sub>o selfbutterket default)\<close>
    unfolding * by simp
  also have \<open>\<dots> = selfbutterket default \<otimes>\<^sub>o c\<close>
    apply (simp del: tensor_butterfly)
    by (simp add: default_prod_def)
  finally have \<open>t1 = selfbutterket default \<otimes>\<^sub>o c\<close>
    by -

  then show ?thesis
    apply (auto intro!: exI[of _ c] simp: regular_register_def t1_def)
    by (metis \<open>bij ((F;G);complement (F;G))\<close> bij_inv_eq_iff)
qed

lemma regular_register_comp: \<open>regular_register (F o G)\<close> if \<open>regular_register F\<close> \<open>regular_register G\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using regular_register_def that by blast+
  from that obtain a where a: \<open>(F; complement F) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default\<close>
    unfolding regular_register_def by metis
  from that obtain b where b: \<open>(G; complement G) (selfbutterket default \<otimes>\<^sub>o b) = selfbutterket default\<close>
    unfolding regular_register_def by metis
  have \<open>complements (F o G) (complement F; F o complement G)\<close>
    by (simp add: complements_chain)
  then have \<open>equivalent_registers (complement F; F o complement G) (complement (F o G))\<close>
    using complement_unique by blast
  then obtain J where [simp]: \<open>iso_register J\<close> and 1: \<open>(complement F; F o complement G) o J = (complement (F o G))\<close>
    using equivalent_registers_def by blast
  have [simp]: \<open>register J\<close>
    by (simp add: iso_register_is_register)

  define c where \<open>c = inv J (a \<otimes>\<^sub>o b)\<close>

  have \<open>((F o G); complement (F o G)) (selfbutterket default \<otimes>\<^sub>o c) = ((F o G); (complement F; F o complement G)) (selfbutterket default \<otimes>\<^sub>o J c)\<close>
    by (auto simp flip: 1 simp: register_pair_apply)
  also have \<open>\<dots> = ((F o (G; complement G); complement F) o assoc' o (id \<otimes>\<^sub>r swap)) (selfbutterket default \<otimes>\<^sub>o J c)\<close>
    apply (subst register_comp_pair[symmetric])
      apply auto[2]
    apply (subst pair_o_assoc')
       apply auto[3]
    apply (subst pair_o_tensor)
    by auto
  also have \<open>\<dots> = ((F o (G; complement G); complement F) o assoc') (selfbutterket default \<otimes>\<^sub>o swap (J c))\<close>
    by auto
  also have \<open>\<dots> = ((F o (G; complement G); complement F) o assoc') (selfbutterket default \<otimes>\<^sub>o (b \<otimes>\<^sub>o a))\<close>
    unfolding c_def apply (subst surj_f_inv_f[where f=J])
    apply (meson \<open>iso_register J\<close> bij_betw_inv_into_right iso_register_inv_comp1 iso_register_inv_comp2 iso_tuple_UNIV_I o_bij surj_iff_all)
    by auto
  also have \<open>\<dots> = (F \<circ> (G;complement G);complement F) ((selfbutterket default \<otimes>\<^sub>o b) \<otimes>\<^sub>o a)\<close>
    by (simp add: assoc'_apply)
  also have \<open>\<dots> = (F; complement F) ((G;complement G) (selfbutterket default \<otimes>\<^sub>o b) \<otimes>\<^sub>o a)\<close>
    by (simp add: register_pair_apply')
  also have \<open>\<dots> = selfbutterket default\<close>
    by (auto simp: a b) 
  finally have \<open>(F \<circ> G;complement (F \<circ> G)) (selfbutterket default \<otimes>\<^sub>o c) = selfbutterket default\<close>
    by -
  then show ?thesis
    using \<open>register F\<close> \<open>register G\<close> register_comp regular_register_def by blast
qed

(* Move to Q_Extra, but with dep on Laws_Compl_Q *)
lemma is_unit_register_empty_var[simp]: \<open>is_unit_register empty_var\<close>
  unfolding is_unit_register_def
  by (auto intro!: same_range_equivalent range_eqI[where x=\<open>id_cblinfun \<otimes>\<^sub>o _\<close>] 
      simp del: id_cblinfun_eq_1 simp flip: iso_register_equivalent_id
      simp: register_pair_apply complements_def)

(* Move to Q_Extra, but with dep on Laws_Compl_Q *)
lemma iso_register_complement_is_unit_register[simp]:
  assumes \<open>iso_register F\<close>
  shows \<open>is_unit_register (complement F)\<close>
  by (meson assms complement_is_complement complements_sym equivalent_complements equivalent_registers_sym is_unit_register_def iso_register_equivalent_id iso_register_is_register)

lemma regular_iso_register:
  assumes \<open>regular_register F\<close>
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>F (selfbutterket default) = selfbutterket default\<close>
proof -
  from assms(1) obtain a where a: \<open>(F;complement F) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default\<close>
    using regular_register_def by blast

  let ?u = \<open>empty_var :: (unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2) \<Rightarrow> _\<close>
  have \<open>is_unit_register ?u\<close> and \<open>is_unit_register (complement F)\<close>
    by auto
  then have \<open>equivalent_registers (complement F) ?u\<close>
    using unit_register_unique by blast
  then obtain I where \<open>iso_register I\<close> and \<open>complement F = ?u o I\<close>
    by (metis \<open>is_unit_register (complement F)\<close> equivalent_registers_def is_unit_register_empty_var unit_register_unique)
  have \<open>selfbutterket default = (F; ?u o I) (selfbutterket default \<otimes>\<^sub>o a)\<close>
    using \<open>complement F = empty_var \<circ> I\<close> a by presburger
  also have \<open>\<dots> = (F; ?u) (selfbutterket default \<otimes>\<^sub>o I a)\<close>
    by (metis \<open>complement F = empty_var \<circ> I\<close> assms(2) comp_apply compatible_complement_right empty_var_compatible' iso_register_is_register register_pair_apply')
  also have \<open>\<dots> = (F; ?u) (selfbutterket default \<otimes>\<^sub>o (one_dim_iso (I a) *\<^sub>C id_cblinfun))\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C (F; ?u) (selfbutterket default \<otimes>\<^sub>o id_cblinfun)\<close>
    by (simp add: Laws_Quantum.register_pair_apply empty_var_def iso_register_is_register)
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C F (selfbutterket default)\<close>
    by (auto simp: register_pair_apply iso_register_is_register simp del: id_cblinfun_eq_1)
  finally have F: \<open>one_dim_iso (I a) *\<^sub>C F (selfbutterket default) = selfbutterket default\<close>
    by simp

  from F have \<open>one_dim_iso (I a) \<noteq> (0::complex)\<close>
    by (metis butterfly_apply butterfly_scaleC_left complex_vector.scale_eq_0_iff id_cblinfun_eq_1 id_cblinfun_not_0 ket_Kronecker_delta_eq ket_nonzero one_dim_iso_of_one one_dim_iso_of_zero')

  have \<open>selfbutterket default = one_dim_iso (I a) *\<^sub>C F (selfbutterket default)\<close>
    using F by simp
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C F (selfbutterket default o\<^sub>C\<^sub>L selfbutterket default)\<close>
    by auto
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C (F (selfbutterket default) o\<^sub>C\<^sub>L F (selfbutterket default))\<close>
    by (simp add: assms(2) iso_register_is_register register_mult)
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C ((selfbutterket default /\<^sub>C one_dim_iso (I a)) o\<^sub>C\<^sub>L (selfbutterket default /\<^sub>C one_dim_iso (I a)))\<close>
    by (metis (no_types, lifting) F \<open>one_dim_iso (I a) \<noteq> 0\<close> complex_vector.scale_left_imp_eq inverse_1 left_inverse scaleC_scaleC zero_neq_one)
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C selfbutterket default\<close>
    by (smt (verit, best) butterfly_comp_butterfly calculation cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right complex_vector.scale_cancel_left ket_Kronecker_delta_eq left_inverse scaleC_one scaleC_scaleC)
  finally have \<open>one_dim_iso (I a) = (1::complex)\<close>
    by (metis butterfly_0_left butterfly_apply complex_vector.scale_cancel_right ket_Kronecker_delta_eq ket_nonzero scaleC_one)
  with F show \<open>F (selfbutterket default) = selfbutterket default\<close>
    by simp
qed

lemma pure_state_nested:
  assumes [simp]: \<open>compatible F G\<close>
  assumes \<open>regular_register H\<close>
  assumes \<open>iso_register H\<close>
  shows \<open>pure_state (F;G) (pure_state H h \<otimes>\<^sub>s g) = pure_state ((F o H);G) (h \<otimes>\<^sub>s g)\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  have [simp]: \<open>register H\<close>
    by (meson assms(3) iso_register_is_register)
  have [simp]: \<open>H (selfbutterket default) = selfbutterket default\<close>
    apply (rule regular_iso_register)
    using assms by auto
  have 1: \<open>pure_state_target_vector H (ket default) = ket default\<close>
    apply (rule pure_state_target_vector_ket_default)
    apply auto
    by (metis (no_types, lifting) ket_Kronecker_delta_eq rangeI scaleC_one)

  have \<open>butterfly (pure_state H h) (ket default) = butterfly (H (butterfly h (ket default)) *\<^sub>V ket default) (ket default)\<close>
    by (simp add: pure_state'_def 1)
  also have \<open>\<dots> = H (butterfly h (ket default)) o\<^sub>C\<^sub>L selfbutterket default\<close>
    by (metis (no_types, hide_lams) adj_cblinfun_compose butterfly_adjoint butterfly_comp_cblinfun double_adj)
  also have \<open>\<dots> = H (butterfly h (ket default)) o\<^sub>C\<^sub>L H (selfbutterket default)\<close>
    by simp
  also have \<open>\<dots> = H (butterfly h (ket default) o\<^sub>C\<^sub>L selfbutterket default)\<close>
    by (meson \<open>register H\<close> register_mult)
  also have \<open>\<dots> = H (butterfly h (ket default))\<close>
    by auto
  finally have 2: \<open>butterfly (pure_state H h) (ket default) = H (butterfly h (ket default))\<close>
    by simp

  show ?thesis
    apply (rule pure_state_eqI)
    using 1 2
    by (auto simp: register_pair_butterfly_tensor compatible_ac_rules default_prod_def simp flip: tensor_ell2_ket)
qed

lemma cblinfun_comp_butterfly: "a o\<^sub>C\<^sub>L butterfly \<psi> \<phi> = butterfly (a *\<^sub>V \<psi>) \<phi>"
  unfolding butterfly_def
  by (simp add: cblinfun_compose_assoc vector_to_cblinfun_applyOp)  

lemma state_apply1: 
  assumes [compatible]: \<open>compatible F G\<close>
  shows \<open>F U *\<^sub>V (F \<psi> \<otimes>\<^sub>p G \<phi>) = (F (U \<psi>) \<otimes>\<^sub>p G \<phi>)\<close>
proof -
  have [compatible]: \<open>compatible F G\<close>
    using assms(1) complements_def by blast
  have \<open>F U *\<^sub>V (F \<psi> \<otimes>\<^sub>p G \<phi>) = (F;G) (U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (F \<psi> \<otimes>\<^sub>p G \<phi>)\<close>
    apply (subst register_pair_apply)
    by auto
  also have \<open>\<dots> = (F (U \<psi>) \<otimes>\<^sub>p G \<phi>)\<close>
    unfolding pure_state'_def 
    by (auto simp: register_mult' cblinfun_comp_butterfly tensor_op_ell2)
  finally show ?thesis
    by -
qed

lemma double_exists: \<open>(\<exists>x y. Q x y) \<longleftrightarrow> (\<exists>z. Q (fst z) (snd z))\<close>
  by simp


(* lemma surj_isometry_is_unitary':
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>isometry U\<close>
  assumes \<open>surj (( *\<^sub>V) U)\<close>
  shows \<open>unitary U\<close>
  using assms(1) apply (rule surj_isometry_is_unitary)
  using assms(2) apply transfer by auto *)

(* TODO: move *)
lemma iso_register_decomposition:
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
proof -
  have [simp]: \<open>register F\<close>
    using assms iso_register_is_register by blast 
  
  let ?ida = \<open>id_cblinfun :: ('a, 'b) complement_domain ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

  from register_decomposition[OF \<open>register F\<close>]
  obtain V :: \<open>('a \<times> ('a, 'b) complement_domain) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary V\<close>
    and FV: \<open>F \<theta> = sandwich V (\<theta> \<otimes>\<^sub>o ?ida)\<close> for \<theta>
    by auto

  have \<open>surj F\<close>
    by (meson assms iso_register_inv_comp2 surj_iff)
  have surj_tensor: \<open>surj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. a \<otimes>\<^sub>o ?ida)\<close>
    apply (rule surj_from_comp[where g=\<open>sandwich V\<close>])
    using \<open>surj F\<close> apply (auto simp: FV)
    by (meson \<open>unitary V\<close> register_inj unitary_sandwich_register)
  then obtain a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close> 
    where a: \<open>a \<otimes>\<^sub>o ?ida = selfbutterket undefined \<otimes>\<^sub>o selfbutterket undefined\<close>
    by (smt (verit, best) surjD)

  then have \<open>a \<noteq> 0\<close>
    apply auto
    by (metis butterfly_apply cblinfun.zero_left complex_vector.scale_eq_0_iff ket_is_orthogonal ket_nonzero)

  obtain \<gamma> where \<gamma>: \<open>?ida = \<gamma> *\<^sub>C selfbutterket undefined\<close>
    apply atomize_elim
    using a \<open>a \<noteq> 0\<close> by (rule tensor_op_almost_injective)
  then have \<open>?ida (ket undefined) = \<gamma> *\<^sub>C (selfbutterket undefined *\<^sub>V ket undefined)\<close>
    by (simp add: \<open>id_cblinfun = \<gamma> *\<^sub>C selfbutterket undefined\<close> scaleC_cblinfun.rep_eq)
  then have \<open>ket undefined = \<gamma> *\<^sub>C ket undefined\<close>
    by (metis butterfly_apply cinner_scaleC_right id_cblinfun_apply ket_Kronecker_delta_eq mult.right_neutral scaleC_one)
  then have \<open>\<gamma> = 1\<close>
    by (smt (z3) \<gamma> butterfly_apply butterfly_scaleC_left cblinfun_id_cblinfun_apply complex_vector.scale_cancel_right ket_Kronecker_delta_eq ket_nonzero)

  define T U where \<open>T = cBlinfun (\<lambda>\<psi>. \<psi> \<otimes>\<^sub>s ket undefined)\<close> and \<open>U = V o\<^sub>C\<^sub>L T\<close>
  have T: \<open>T \<psi> = \<psi> \<otimes>\<^sub>s ket undefined\<close> for \<psi>
    unfolding T_def
    apply (subst bounded_clinear_cBlinfun_apply)
    by (auto intro!: bounded_clinear_finite_dim clinear_tensor_ell22)
  have sandwich_T: \<open>sandwich T a = a \<otimes>\<^sub>o ?ida\<close> for a
    apply (rule fun_cong[where x=a])
    apply (rule clinear_eq_butterfly_ketI)
      apply auto
    by (metis (no_types, hide_lams) Misc.sandwich_def T \<gamma> \<open>\<gamma> = 1\<close> adj_cblinfun_compose butterfly_adjoint cblinfun_comp_butterfly scaleC_one tensor_butterfly)

  have \<open>F (butterfly x y) = V o\<^sub>C\<^sub>L (butterfly x y \<otimes>\<^sub>o ?ida) o\<^sub>C\<^sub>L V*\<close> for x y
    by (simp add: Misc.sandwich_def FV)
  also have \<open>\<dots> x y = V o\<^sub>C\<^sub>L (butterfly (T x) (T y)) o\<^sub>C\<^sub>L V*\<close> for x y
    by (simp add: T \<gamma> \<open>\<gamma> = 1\<close>)
  also have \<open>\<dots> x y = U o\<^sub>C\<^sub>L (butterfly x y) o\<^sub>C\<^sub>L U*\<close> for x y
    by (simp add: U_def butterfly_comp_cblinfun cblinfun_comp_butterfly)
  finally have F_rep:  \<open>F a = U o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L U*\<close> for a
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac clinear_eq_butterfly_ketI)
    apply auto
    by (metis (no_types, lifting) cblinfun_apply_clinear clinear_iff sandwich_apply)

  have \<open>isometry T\<close>
    apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: T)
  moreover have \<open>T *\<^sub>S \<top> = \<top>\<close>
  proof -
    have 1: \<open>\<phi> \<otimes>\<^sub>s \<xi> \<in> range ((*\<^sub>V) T)\<close> for \<phi> \<xi>
    proof -
      have \<open>T *\<^sub>V (cinner (ket undefined) \<xi> *\<^sub>C \<phi>) = \<phi> \<otimes>\<^sub>s (cinner (ket undefined) \<xi> *\<^sub>C ket undefined)\<close>
        by (simp add: T tensor_ell2_scaleC2)
      also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (selfbutterket undefined *\<^sub>V \<xi>)\<close>
        by simp
      also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (?ida *\<^sub>V \<xi>)\<close>
        by (simp add: \<gamma> \<open>\<gamma> = 1\<close>)
      also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<xi>\<close>
        by simp
      finally show ?thesis
        by (metis range_eqI)
    qed

    have \<open>\<top> \<le> ccspan {ket x | x. True}\<close>
      by (simp add: full_SetCompr_eq)
    also have \<open>\<dots> \<le> ccspan {\<phi> \<otimes>\<^sub>s \<xi> | \<phi> \<xi>. True}\<close>
      apply (rule ccspan_mono)
      by (auto simp flip: tensor_ell2_ket)
    also from 1 have \<open>\<dots> \<le> ccspan (range ((*\<^sub>V) T))\<close>
      by (auto intro!: ccspan_mono)
    also have \<open>\<dots> = T *\<^sub>S \<top>\<close>
      by (metis (mono_tags, hide_lams) calculation cblinfun_image_Span cblinfun_image_mono eq_iff top_greatest)
    finally show \<open>T *\<^sub>S \<top> = \<top>\<close>
      using top.extremum_uniqueI by blast
  qed

  ultimately have \<open>unitary T\<close>
    by (rule surj_isometry_is_unitary)
  then have \<open>unitary U\<close>
    by (simp add: U_def \<open>unitary V\<close>)

  from F_rep \<open>unitary U\<close> show ?thesis
    by (auto simp: sandwich_def[abs_def])
qed

lemma cspan_state: 
  assumes \<open>iso_register F\<close>
  assumes \<open>cspan (g ` X) = UNIV\<close>
  assumes \<eta>_cond: \<open>F (selfbutter \<eta>) *\<^sub>V pure_state_target_vector F \<eta> \<noteq> 0\<close>
  shows \<open>cspan ((\<lambda>z. pure_state' F (g z) \<eta>) ` X) = UNIV\<close>
proof -
  from iso_register_decomposition[of F]
  obtain U where [simp]: \<open>unitary U\<close> and F: \<open>F = sandwich U\<close>
    using assms(1) by blast

  define \<eta>' c where \<open>\<eta>' = pure_state_target_vector F \<eta>\<close> and \<open>c = cinner (U *\<^sub>V \<eta>) \<eta>'\<close>

  from \<eta>_cond
  have \<open>c \<noteq> 0\<close>
    by (simp add: \<eta>'_def F sandwich_def c_def cinner_adj_right)

  have \<open>cspan ((\<lambda>z. pure_state' F (g z) \<eta>) ` X) = cspan ((\<lambda>z. F (butterfly (g z) \<eta>) *\<^sub>V \<eta>') ` X)\<close>
    by (simp add: \<eta>'_def pure_state'_def)
  also have \<open>\<dots> = cspan ((\<lambda>z. (butterfly (U *\<^sub>V g z) (U *\<^sub>V \<eta>)) *\<^sub>V \<eta>') ` X)\<close>
    by (simp add: F sandwich_def cinner_adj_right)
  also have \<open>\<dots> = cspan ((\<lambda>z. c *\<^sub>C U *\<^sub>V g z) ` X)\<close>
    by (simp add: c_def)
  also have \<open>\<dots> = (\<lambda>z. c *\<^sub>C U *\<^sub>V z) ` cspan (g ` X)\<close>
    apply (subst complex_vector.linear_span_image[symmetric])
    by (auto simp: image_image)
  also have \<open>\<dots> = (\<lambda>z. c *\<^sub>C U *\<^sub>V z) ` UNIV\<close>
    using assms(2) by presburger
  also have \<open>\<dots> = UNIV\<close>
    apply (rule surjI[where f=\<open>\<lambda>z. (U* *\<^sub>V z) /\<^sub>C c\<close>])
    using \<open>c \<noteq> 0\<close> by (auto simp flip: cblinfun_apply_cblinfun_compose)
  finally show ?thesis
    by -
qed

lemma cspan_state': 
  assumes [simp]: \<open>iso_register F\<close>
  assumes \<open>cspan (g ` X) = UNIV\<close>
  shows \<open>cspan ((\<lambda>z. pure_state F (g z)) ` X) = UNIV\<close>
  apply (rule cspan_state)
  using assms apply auto[2]
  apply (rule pure_state_target_vector_correct)
  by (auto simp: iso_register_is_register)

method pure_state_eq = 
  (rule pure_state_eqI;
    auto simp: pure_state_nested register_pair_butterfly_tensor compatible_ac_rules default_prod_def simp flip: tensor_ell2_ket)

(* Example *)
lemma example3:
  fixes F :: \<open>bit update \<Rightarrow> 'c::{finite,default} update\<close>
    and G :: \<open>bit update \<Rightarrow> 'c update\<close>
  assumes [compatible]: \<open>compatible F G\<close>
  shows  \<open>(F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT = (F;G) swap_ell2\<close>
proof -
  define Z where \<open>Z = complement (F;G)\<close>
  then have [compatible]: \<open>compatible Z F\<close> \<open>compatible Z G\<close>
    using assms compatible_complement_pair1 compatible_complement_pair2 compatible_sym by blast+

  have [simp]: \<open>iso_register (F;(G;Z))\<close>
    using Z_def assms complements_complement_pair complements_def by blast
  
  have eq1: \<open>((F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT) *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))
           = (F;G) swap_ell2 *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))\<close> for f g z
  proof -
    have \<open>(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = ((F;G) (ket f \<otimes>\<^sub>s ket g) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    also have \<open>(F;G) CNOT *\<^sub>V \<dots> = ((F;G) (ket f \<otimes>\<^sub>s ket (g+f)) \<otimes>\<^sub>p Z(ket z))\<close>
      apply (subst state_apply1) by auto
    also have \<open>\<dots> = ((G;F) (ket (g+f) \<otimes>\<^sub>s ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    also have \<open>(G;F) CNOT *\<^sub>V \<dots> = ((G;F) (ket (g+f) \<otimes>\<^sub>s ket g) \<otimes>\<^sub>p Z ket z)\<close>
      apply (subst state_apply1) by auto
    also have \<open>\<dots> = ((F;G) (ket g \<otimes>\<^sub>s ket (g+f)) \<otimes>\<^sub>p Z ket z)\<close>
      by pure_state_eq
    also have \<open>(F;G) CNOT *\<^sub>V \<dots> = ((F;G) ket g \<otimes>\<^sub>s ket f \<otimes>\<^sub>p Z ket z)\<close>
      apply (subst state_apply1) by auto
    also have \<open>\<dots> = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    finally have 1: \<open>((F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT) *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by auto

    have \<open>(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = ((F;G) (ket f \<otimes>\<^sub>s ket g) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    also have \<open>(F;G) swap_ell2 *\<^sub>V \<dots> = ((F;G) (ket g \<otimes>\<^sub>s ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by (auto simp: state_apply1 swap_ell2_tensor simp del: tensor_ell2_ket)
    also have \<open>\<dots> = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    finally have 2: \<open>(F;G) swap_ell2 *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by -

    from 1 2 show ?thesis
      by simp
  qed

  then have eq1: \<open>((F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT) *\<^sub>V \<psi>
           = (F;G) swap_ell2 *\<^sub>V \<psi>\<close> if \<open>\<psi> \<in> {(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))| f g z. True}\<close> for \<psi>
    using that by auto

  moreover have \<open>cspan {(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))| f g z. True} = UNIV\<close>
    (* TODO make this one nicer *)
    apply (simp only: double_exists setcompr_eq_image full_SetCompr_eq)
    apply simp
    apply (rule cspan_state')
    by auto

  ultimately show ?thesis
    using cblinfun_eq_on_UNIV_span by blast
qed

end
