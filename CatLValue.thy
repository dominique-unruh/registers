theory CatLValue
  imports CatLValue_Axioms2
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
  by (simp add: assms)

definition "chain x y = x o\<^sub>l y"

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

lemma lvalue_app_fun_cong: "f = g \<Longrightarrow> f \<cdot> x = g \<cdot> x" by simp

lemma compatible3:
  assumes [simp]: (* "compatible x y" and *) "compatible y z" and "compatible x z"
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

definition is_everything1 where
  "is_everything1 x \<longleftrightarrow> (\<exists>y. \<forall>f. (y o\<^sub>l x) \<cdot> f = f)"

definition is_everything2 where
  "is_everything2 x \<longleftrightarrow> inj (lvalue_app x)"

definition is_complement1 where
  "is_complement1 x y \<longleftrightarrow> compatible x y \<and> is_everything1 (pair x y)"

definition is_complement2 where
  "is_complement2 x y \<longleftrightarrow> compatible x y \<and> is_everything2 (pair x y)"

lemma complement_chain1:
  assumes "is_complement1 x x'"
  assumes "is_complement1 y y'"
  shows "is_complement1 (chain x y) (pair (chain x y') x')"
proof (simp add: is_complement1_def, rule)
  have [simp]: "compatible x x'" "compatible y y'" "compatible x' x" "compatible y' y"
    using assms is_complement1_def compatible_sym by blast+
  show "compatible (chain x y) (pair (chain x y') x')"
    apply (rule compatible_sym)
    apply (rule compatible3)
    apply (rule compatible_sym)
    apply (rule compatible_chain_left, simp)
    by (rule compatible_chain_inner, simp)
  from assms(1)
  obtain xInv where "xInv o\<^sub>l pair x x' \<cdot> f = f" for f
    unfolding is_complement1_def is_everything1_def by auto
  from assms(2)
  obtain yInv where "yInv o\<^sub>l pair y y' \<cdot> f = f" for f
    unfolding is_complement1_def is_everything1_def by auto
  show "is_everything1 (pair (chain x y) (pair (chain x y') x'))"
    unfolding is_everything1_def apply (rule exI[of _ ])
  (* TODO: need something to connect pair x (pair y z) with
    pair (pair x y) z. \<longrightarrow> assoc

    And maybe pair x y with pair y z (\<rightarrow> this one is done by swap).
  *)
    sorry
qed


lemma complement_chain2:
  assumes "is_complement2 x x'"
  assumes "is_complement2 y y'"
  shows "is_complement2 (chain x y) (pair (chain x y') x')"
  sorry