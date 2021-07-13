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

definition is_unit_register where
  \<open>is_unit_register U \<longleftrightarrow> compatible U id \<and> equivalent_registers id (U; id)\<close>

lemma register_unit_register[simp]: \<open>is_unit_register U \<Longrightarrow> register U\<close>
  by (simp add: compatible_def is_unit_register_def)

lemma unit_register_compatible[simp]: \<open>compatible U X\<close> if \<open>is_unit_register U\<close> \<open>register X\<close>
  by (metis compatible_comp_right id_comp is_unit_register_def that(1) that(2))


lemma equivalent_registersI:
  assumes \<open>register F\<close>
  assumes \<open>iso_register I\<close>
  assumes \<open>F o I = G\<close>
  shows \<open>equivalent_registers F G\<close>
  using assms unfolding equivalent_registers_def by blast

lemma equivalent_registers_trans[trans]: 
  assumes \<open>equivalent_registers F G\<close> and \<open>equivalent_registers G H\<close>
  shows \<open>equivalent_registers F H\<close>
proof -
  from assms have [simp]: \<open>register F\<close> \<open>register G\<close>
    by (auto simp: equivalent_registers_def)
  from assms(1) obtain I where [simp]: \<open>iso_register I\<close> and \<open>F o I = G\<close>
    using equivalent_registers_def by blast
  from assms(2) obtain J where [simp]: \<open>iso_register J\<close> and \<open>G o J = H\<close>
    using equivalent_registers_def by blast
  have \<open>register F\<close>
    by (auto simp: equivalent_registers_def)
  moreover have \<open>iso_register (I o J)\<close>
    using \<open>iso_register I\<close> \<open>iso_register J\<close> iso_register_comp by blast
  moreover have \<open>F o (I o J) = H\<close>
    by (simp add: \<open>F \<circ> I = G\<close> \<open>G \<circ> J = H\<close> o_assoc)
  ultimately show ?thesis
    by (rule equivalent_registersI)
qed

lemma register_tensor_id_id[simp]: \<open>id \<otimes>\<^sub>r id = id\<close>
  by (simp add: register_tensor_is_hom tensor_extensionality)

lemma equivalent_registers_pair_right:
  assumes [simp]: \<open>compatible F G\<close>
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

lemma equivalent_registers_pair_left:
  assumes [simp]: \<open>compatible F G\<close>
  assumes eq: \<open>equivalent_registers F H\<close>
  shows \<open>equivalent_registers (F;G) (H;G)\<close>
proof -
  from eq obtain I where [simp]: \<open>iso_register I\<close> and \<open>F o I = H\<close>
    by (metis equivalent_registers_def)
  then have *: \<open>(F;G) \<circ> (I \<otimes>\<^sub>r id) = (H;G)\<close>
    by (auto intro!: tensor_extensionality register_comp register_preregister register_tensor_is_hom 
        simp:  register_pair_apply iso_register_is_register)
  show ?thesis
    apply (rule equivalent_registersI[where I=\<open>I \<otimes>\<^sub>r id\<close>])
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

lemma unit_register_pair[simp]: \<open>equivalent_registers X (U; X)\<close> if [simp]: \<open>is_unit_register U\<close> \<open>register X\<close>
proof -
  have \<open>equivalent_registers id (U; id)\<close>
    using is_unit_register_def that(1) by blast
  also have \<open>equivalent_registers \<dots> (U; (X; complement X))\<close>
    apply (rule equivalent_registers_pair_right)
    apply (auto intro!: unit_register_compatible)
    using complement_is_complement complements_def equivalent_registersI id_comp register_id that(2) by blast
  also have \<open>equivalent_registers \<dots> ((U; X); complement X)\<close>
    apply (rule equivalent_registers_assoc)
    by auto
  finally have \<open>complements (U; X) (complement X)\<close>
    by (auto simp: equivalent_registers_def complements_def)
  moreover have \<open>equivalent_registers (X; complement X) id\<close>
    by (metis complement_is_complement complements_def equivalent_registers_def iso_register_def that)
  ultimately show ?thesis
    by (meson complement_unique complement_is_complement complements_sym equivalent_registers_sym equivalent_registers_trans that)
qed

lemma equivalent_registers_comp:
  assumes \<open>equivalent_registers F G\<close>
  assumes \<open>register H\<close>
  shows \<open>equivalent_registers (H o F) (H o G)\<close>
  by (metis (no_types, lifting) assms(1) assms(2) comp_assoc equivalent_registers_def register_comp)

lemma unit_register_compose_left:
  assumes [simp]: \<open>is_unit_register U\<close>
  assumes [simp]: \<open>register A\<close>
  shows \<open>is_unit_register (A o U)\<close>
proof -
  have \<open>compatible (A o U) (A; complement A)\<close>
    apply (auto intro!: compatible3')
    by (metis assms(1) assms(2) comp_id compatible_comp_inner is_unit_register_def)
  then have compat[simp]: \<open>compatible (A o U) id\<close>
    by (metis assms(2) compatible_comp_right complement_is_complement complements_def iso_register_def)
  have \<open>equivalent_registers (A o U; id) (A o U; (A; complement A))\<close>
    apply (auto intro!: equivalent_registers_pair_right)
    using assms(2) complement_is_complement complements_def equivalent_registers_def id_comp register_id by blast
  also have \<open>equivalent_registers \<dots> ((A o U; A o id); complement A)\<close>
    apply auto
    by (metis (no_types, hide_lams) compat assms(1) assms(2) compatible_comp_left compatible_def compatible_register1 complement_is_complement complements_def equivalent_registers_assoc id_apply register_unit_register)
  also have \<open>equivalent_registers \<dots> (A o (U; id); complement A)\<close>
    by (metis (no_types, lifting) assms(1) assms(2) calculation equivalent_registers_sym equivalent_registers_trans is_unit_register_def register_comp_pair)
  also have \<open>equivalent_registers \<dots> (A o id; complement A)\<close>
    apply (intro equivalent_registers_pair_left equivalent_registers_comp)
    apply (auto simp: assms)
    using assms(1) equivalent_registers_sym register_id unit_register_pair by blast
  also have \<open>equivalent_registers \<dots> id\<close>
    by (metis assms(2) comp_id complement_is_complement complements_def equivalent_registers_def iso_register_inv iso_register_inv_comp2 pair_is_register)
  finally show ?thesis
    using compat equivalent_registers_sym is_unit_register_def by blast
qed

lemma unit_register_compose_right:
  assumes [simp]: \<open>is_unit_register U\<close>
  assumes [simp]: \<open>iso_register A\<close>
  shows \<open>is_unit_register (U o A)\<close>
proof (unfold is_unit_register_def, intro conjI)
  show \<open>compatible (U \<circ> A) id\<close>
    using assms(1) assms(2) compatible_comp_left is_unit_register_def iso_register_is_register by blast
  have 1: \<open>iso_register ((U;id) \<circ> A \<otimes>\<^sub>r id)\<close>
    by (metis assms(1) assms(2) equivalent_registers_def is_unit_register_def iso_register_comp iso_register_id iso_register_tensor_is_iso_register)
  have 2: \<open>id \<circ> ((U;id) \<circ> A \<otimes>\<^sub>r id) = (U \<circ> A;id)\<close>
    by (metis assms(1) assms(2) fun.map_id is_unit_register_def iso_register_is_register pair_o_tensor register_id)
  show \<open>equivalent_registers id (U \<circ> A;id)\<close>
    apply (rule equivalent_registersI[where I=\<open>(U;id) \<circ> (A \<otimes>\<^sub>r id)\<close>])
    using 1 2 by auto
qed

lemma unit_register_unique:
  assumes \<open>is_unit_register F\<close>
  assumes \<open>is_unit_register G\<close>
  shows \<open>equivalent_registers F G\<close>
proof -
  have \<open>complements F id\<close> \<open>complements G id\<close>
    using assms by (metis complements_def equivalent_registers_def id_comp is_unit_register_def)+
  then show ?thesis
    by (meson complement_unique complements_sym equivalent_registers_sym equivalent_registers_trans)
qed

lemma unit_register_domains_isomorphic:
  fixes F :: \<open>'a::domain update \<Rightarrow> 'c::domain update\<close>
  fixes G :: \<open>'b::domain update \<Rightarrow> 'd::domain update\<close>
  assumes \<open>is_unit_register F\<close>
  assumes \<open>is_unit_register G\<close>
  shows \<open>\<exists>I :: 'a update \<Rightarrow> 'b update. iso_register I\<close>
proof -
  have \<open>is_unit_register ((\<lambda>d. tensor_update id_update d) o G)\<close>
    by (simp add: assms(2) unit_register_compose_left)
  moreover have \<open>is_unit_register ((\<lambda>c. tensor_update c id_update) o F)\<close>
    using assms(1) register_tensor_left unit_register_compose_left by blast
  ultimately have \<open>equivalent_registers ((\<lambda>d. tensor_update id_update d) o G) ((\<lambda>c. tensor_update c id_update) o F)\<close>
    using unit_register_unique by blast
  then show ?thesis
    unfolding equivalent_registers_def by auto
qed


lemma id_complement_is_unit_register[simp]: \<open>is_unit_register (complement id)\<close>
  by (metis is_unit_register_def complement_is_complement complements_def complements_sym equivalent_registers_def id_comp register_id)

type_synonym unit_register_domain = \<open>(some_domain, some_domain) complement_domain\<close>
definition unit_register :: \<open>unit_register_domain update \<Rightarrow> 'a::domain update\<close> where \<open>unit_register = (SOME U. is_unit_register U)\<close>

lemma unit_register_is_unit_register[simp]: \<open>is_unit_register (unit_register :: unit_register_domain update \<Rightarrow> 'a::domain update)\<close>
proof -
  let ?U0 = \<open>complement id :: unit_register_domain update \<Rightarrow> some_domain update\<close>
  let ?U1 = \<open>complement id :: ('a, 'a) complement_domain update \<Rightarrow> 'a update\<close>
  have \<open>is_unit_register ?U0\<close> \<open>is_unit_register ?U1\<close>
    by auto
  then obtain I :: \<open>unit_register_domain update \<Rightarrow> ('a, 'a) complement_domain update\<close> where \<open>iso_register I\<close>
    apply atomize_elim by (rule unit_register_domains_isomorphic)
  with \<open>is_unit_register ?U1\<close> have \<open>is_unit_register (?U1 o I)\<close>
    by (rule unit_register_compose_right)
  then show ?thesis
    by (metis someI_ex unit_register_def)
qed

lemma unit_register_domain_tensor_unit:
  fixes U :: \<open>'a::domain update \<Rightarrow> _\<close>
  assumes \<open>is_unit_register U\<close>
  shows \<open>\<exists>I :: 'b::domain update \<Rightarrow> ('a*'b) update. iso_register I\<close>
       (* Can we show that I = (\<lambda>x. tensor_update id_update x) ? *)
proof -
  have \<open>equivalent_registers (id :: 'b update \<Rightarrow> _) (complement id; id)\<close>
    by auto
  then obtain J :: \<open>'b update \<Rightarrow> ((('b, 'b) complement_domain * 'b) update)\<close> where \<open>iso_register J\<close>
    using equivalent_registers_def iso_register_inv by blast
  moreover obtain K :: \<open>('b, 'b) complement_domain update \<Rightarrow> 'a update\<close> where \<open>iso_register K\<close>
    using assms id_complement_is_unit_register unit_register_domains_isomorphic by blast
  ultimately have \<open>iso_register ((K \<otimes>\<^sub>r id) o J)\<close>
    by auto
  then show ?thesis   
    by auto
qed

end
