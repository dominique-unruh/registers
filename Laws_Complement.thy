section \<open>Generic laws about complements\<close>

theory Laws_Complement
  imports Laws Axioms_Complement
begin

definition \<open>complements F G \<longleftrightarrow> compatible F G \<and> iso_register (F;G)\<close>

lemma complements_sym: \<open>complements G F\<close> if \<open>complements F G\<close>
proof -
  from that have \<open>iso_register (F;G)\<close>
    by (meson complements_def)
  then obtain I where [simp]: \<open>register I\<close> and \<open>(F;G) o I = id\<close> and \<open>I o (F;G) = id\<close>
    using iso_register_def by blast
  have \<open>register (swap o I)\<close>
    using \<open>register I\<close> register_comp register_swap by blast
  moreover have \<open>(G;F) o (swap o I) = id\<close>
    by (metis (no_types, hide_lams) \<open>(F;G) \<circ> I = id\<close> compatible_def complements_def pair_o_swap rewriteL_comp_comp that)
  moreover have \<open>(swap o I) o (G;F) = id\<close>
    by (metis (no_types, hide_lams) swap_swap \<open>I \<circ> (F;G) = id\<close> calculation(2) comp_def eq_id_iff)
  ultimately have \<open>iso_register (G;F)\<close>
    using compatible_sym complements_def iso_registerI pair_is_register that by blast
  then show \<open>complements G F\<close>
    by (meson compatible_sym complements_def that)
qed

definition complement :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> (('a,'b) complement_domain update \<Rightarrow> 'b update)\<close> where
  \<open>complement F = (SOME G :: ('a, 'b) complement_domain update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G))\<close>

lemma register_complement[simp]: \<open>register (complement F)\<close> if \<open>register F\<close>
  using complement_exists[OF that]
  by (metis (no_types, lifting) compatible_def complement_def some_eq_imp)

lemma complement_is_complement:
  assumes \<open>register F\<close>
  shows \<open>complements F (complement F)\<close>
  using complement_exists[OF assms] unfolding complements_def
  by (metis (mono_tags, lifting) complement_def some_eq_imp)

lemma complement_unique:
  assumes \<open>complements F G\<close>
  shows \<open>equivalent_registers G (complement F)\<close>
  apply (rule complement_unique[where F=F])
  using assms unfolding complements_def using compatible_register1 complement_is_complement complements_def by blast+

definition unit_register where \<open>unit_register = complement id\<close>

lemma register_unit_register[simp]: \<open>register unit_register\<close>
  unfolding unit_register_def
  by (auto intro: register_complement)

lemma unit_register_compatible[simp]: \<open>compatible unit_register X\<close> if \<open>register X\<close>
proof -
  have \<open>compatible unit_register (id o X)\<close>
    by (metis compatible_comp_left compatible_sym complement_is_complement complements_def register_id that unit_register_def)
  then show ?thesis
    by simp
qed

lemma equivalent_registers_trans[trans]: 
  assumes \<open>equivalent_registers F G\<close> and \<open>equivalent_registers G H\<close>
  shows \<open>equivalent_registers F H\<close>
  sorry

lemma equivalent_registersI:
  assumes \<open>register F\<close>
  assumes \<open>iso_register I\<close>
  assumes \<open>F o I = G\<close>
  shows \<open>equivalent_registers F G\<close>
  using assms unfolding equivalent_registers_def by blast

lemma iso_register_is_register: \<open>iso_register F \<Longrightarrow> register F\<close>
  using iso_register_def by blast

lemma register_tensor_distrib:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close> \<open>register H\<close> \<open>register L\<close>
  shows \<open>(F \<otimes>\<^sub>r G) o (H \<otimes>\<^sub>r L) = (F o H) \<otimes>\<^sub>r (G o L)\<close>
  apply (rule tensor_extensionality)
  by (auto intro!: register_comp register_preregister register_tensor_is_hom)

lemma register_tensor_id_id[simp]: \<open>id \<otimes>\<^sub>r id = id\<close>
  by (simp add: register_tensor_is_hom tensor_extensionality)

lemma iso_register_tensor_is_iso_register:
  assumes [simp]: \<open>iso_register F\<close> \<open>iso_register G\<close>
  shows \<open>iso_register (F \<otimes>\<^sub>r G)\<close>
proof -
  from assms obtain F' G' where [simp]: \<open>register F'\<close> \<open>register G'\<close> \<open>F o F' = id\<close> \<open>F' o F = id\<close>
    \<open>G o G' = id\<close> \<open>G' o G = id\<close>
    by (meson iso_register_def)
  show ?thesis
    apply (rule iso_registerI[where G=\<open>F' \<otimes>\<^sub>r G'\<close>])
    by (auto simp: register_tensor_is_hom iso_register_is_register register_tensor_distrib)
qed

lemma iso_register_id[simp]: \<open>iso_register id\<close>
  by (simp add: iso_register_def)

lemma equivalent_registers_pair_right:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible F H\<close>
  assumes eq: \<open>equivalent_registers G H\<close>
  shows \<open>equivalent_registers (F;G) (F;H)\<close>
proof -
  from eq obtain I where [simp]: \<open>iso_register I\<close> and \<open>G o I = H\<close>
    by (metis equivalent_registers_def)
  then have *: \<open>(F;G) \<circ> (id \<otimes>\<^sub>r I) = (F;H)\<close>
    by (auto intro!: tensor_extensionality register_comp register_preregister register_tensor_is_hom 
        simp:  register_pair_apply iso_register_is_register)
  show ?thesis
    apply (rule equivalent_registersI[where I=\<open>id \<otimes>\<^sub>r I\<close>])
    using * by (auto intro!: iso_register_tensor_is_iso_register)
qed

lemma iso_register_assoc[simp]: \<open>iso_register assoc\<close>
  apply (rule iso_registerI[where G=assoc'])
  by (auto simp add: assoc'_apply assoc_apply tensor_extensionality3 tensor_extensionality3')

lemma equivalent_registers_assoc[simp]:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible F H\<close> \<open>compatible G H\<close>
  shows \<open>equivalent_registers (F;(G;H)) ((F;G);H)\<close>
  apply (rule equivalent_registersI[where I=assoc])
  by auto

lemma compatible_complement_left[simp]: \<open>register X \<Longrightarrow> compatible (complement X) X\<close>
  using compatible_sym complement_is_complement complements_def by blast

lemma compatible_complement_right[simp]: \<open>register X \<Longrightarrow> compatible X (complement X)\<close>
  using complement_is_complement complements_def by blast

lemma unit_register_pair[simp]: \<open>equivalent_registers X (unit_register; X)\<close> if [simp]: \<open>register X\<close>
proof -
  have \<open>equivalent_registers id (unit_register; id)\<close>
    by (metis complement_is_complement complements_def complements_sym equivalent_registers_def id_comp register_id unit_register_def)
  also have \<open>equivalent_registers \<dots> (unit_register; (X; complement X))\<close>
    apply (rule equivalent_registers_pair_right)
    apply (auto intro!: unit_register_compatible)
    by (metis complement_is_complement complements_def equivalent_registers_def equivalent_registers_sym iso_register_def that)
  also have \<open>equivalent_registers \<dots> ((unit_register; X); complement X)\<close>
    apply (rule equivalent_registers_assoc)
    by auto
  finally have \<open>complements (unit_register; X) (complement X)\<close>
    by (auto simp: equivalent_registers_def complements_def)
  moreover have \<open>equivalent_registers (X; complement X) id\<close>
    by (metis complement_is_complement complements_def equivalent_registers_def iso_register_def that)
  ultimately show ?thesis
    by (meson complement_unique complement_is_complement complements_sym equivalent_registers_sym equivalent_registers_trans that)
qed

(* TODO: Do we have an iso between [in-space of unit_register] \<otimes> A and A? (Where A is an update monoid) 
   The <- direction would be (\<lambda>x. id_update \<otimes> x). 
  It follows from unit_register_pair, but not for all possible instantiations of the types.

Maybe a first step would be to show that unit_register o unit_register -equiv- unit_register.
Or better unit_register o A -equiv- unit_register.
*)

lemma unit_register_unique:
  assumes \<open>compatible F id\<close>
  assumes \<open>equivalent_registers id (F; id)\<close>
  shows \<open>equivalent_registers F unit_register\<close>
  using assms by (metis complement_unique complements_def complements_sym equivalent_registers_def id_comp unit_register_def)

end
