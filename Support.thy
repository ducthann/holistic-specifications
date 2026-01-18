theory Support
  imports Main 
(*Author: Duc Than Nguyen *)
begin
lemma Greatest_eq [simp]:
  "(GREATEST x. x = (a::nat)) = a"
  by (simp add: Greatest_equality)

lemma sorted_head:
  "sorted xs \<Longrightarrow>  x \<in> set xs \<Longrightarrow>  hd xs \<le> x"
  by(induction xs arbitrary: x, auto)

lemma sorted_last:
  "sorted xs \<Longrightarrow>  x \<in> set xs \<Longrightarrow>  last xs \<ge> x"
  by(induction xs arbitrary: x, auto)

lemma last_sorted_list_of_list_is_greatest:
  assumes fin: "finite A"
  assumes yin: "(y::nat) \<in> A"
  shows "y \<le> last (sorted_list_of_set A)"
  by (simp add: fin sorted_last yin)

lemma not_eq_a: 
"finite A \<Longrightarrow> Suc (last (sorted_list_of_set (insert a A))) \<noteq> a"
  by (metis Suc_n_not_le_n finite.insertI insertI1 
      last_sorted_list_of_list_is_greatest)

lemma not_in_A: 
"finite A \<Longrightarrow> Suc (last (sorted_list_of_set (insert a A))) \<notin> A" 
  by (meson Suc_n_not_le_n finite.simps insertI2 
      last_sorted_list_of_list_is_greatest)
end