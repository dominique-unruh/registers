theory CatLValue
  imports CatLValue_Axioms
begin

definition 
  \<open>compatible x y \<longleftrightarrow> (\<forall>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f))\<close>

definition
  \<open>pair x y = (THE xy. \<forall>f g. xy \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g))\<close>

lemma pair_apply[simp]: 
  shows "pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)"
  unfolding pair_def apply (rule the1I2[where P="\<lambda>xy. \<forall>f g. xy \<cdot> f \<otimes> g = (x \<cdot> f) o\<^sub>m (y \<cdot> g)"])
  by (auto simp add: pair_exists tensor_extensionality)

lemma compatibleI: 
  assumes "\<And>f g. pair x y \<cdot> (f \<otimes> g) = pair y x \<cdot> (g \<otimes> f)"
  shows "compatible x y"
  using assms unfolding compatible_def by simp

lemma compatibleI':
  assumes "pair x y = pair y x o\<^sub>l swap"
  shows "compatible x y"
  apply (rule compatibleI)
  by (simp add: assms swap_apply lvalue_comp_app)

definition "chain x y = x o\<^sub>l y"

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

lemma lvalue_app_fun_cong: "f = g \<Longrightarrow> f \<cdot> x = g \<cdot> x" by simp

lemma compatible3:
  assumes [simp]: "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible (pair x y) z"
proof -
  have "pair (pair x y) z \<cdot> (f \<otimes> g) \<otimes> h = pair z (pair x y) \<cdot> h \<otimes> (f \<otimes> g)" for f g h
    apply auto using assms unfolding compatible_def
    by (metis maps_comp_assoc)
  then have "(pair (pair x y) z o\<^sub>l swap o\<^sub>l left_tensor h) \<cdot> (f \<otimes> g)
           = (pair z (pair x y) o\<^sub>l left_tensor h) \<cdot> (f \<otimes> g)" for f g h
    by auto
  then have *: "(pair (pair x y) z o\<^sub>l swap o\<^sub>l left_tensor h)
           = (pair z (pair x y) o\<^sub>l left_tensor h)" for h
    by (rule tensor_extensionality)
  have "(pair (pair x y) z) \<cdot> (fg \<otimes> h)
           = (pair z (pair x y)) \<cdot> (h \<otimes> fg)" for fg h
    using *[THEN lvalue_app_fun_cong]
    by auto
  then show ?thesis
    unfolding compatible_def by simp
qed

lemma compatible_chain_left: "compatible x y \<Longrightarrow> compatible (chain x z) y"
  unfolding compatible_def chain_def lvalue_comp_app by auto
  
lemma compatible_chain_inner: 
  "compatible x y \<Longrightarrow> compatible (chain z x) (chain z y)"
  unfolding compatible_def chain_def  
  by (auto simp flip: lvalue_app_mult)

