theory Deterministic
  imports Deterministic_Aux
begin
text\<open>Finally, we conclude that @{term internal_exec_det} is deterministic.
It is one of the main lemmas needed to show that the visible-states semantics is deterministic.\<close>

text \<open>Lemma @{term internal_exec_det} says that 
in the first @{term "n-(2::nat)"} steps of execution 
if for the same initial state @{term \<sigma>}, 
there is at most one next state that is reached after one step of execution, i.e., 
if @{term "\<sigma>"} steps to @{term "\<sigma>'"} and also to @{term "v"}, then @{term "v = \<sigma>'"}.\<close>
lemma internal_exec_det:
 "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>' \<Longrightarrow> M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> v \<Longrightarrow>  v = \<sigma>'"
  by (auto simp: internal_exec_det_aux)

text\<open>Lemma @{term visible_exec_det} asserts that the execution of the visible-states semantics is 
deterministic as below. Similar to Lemma @{term internal_exec_det}, 
Lemma @{term visible_exec_det} also says that 
if @{term "\<sigma>"} steps to @{term "\<sigma>'"} and also to @{term "\<sigma>''"}, then @{term "\<sigma>'' = \<sigma>'"},
but in this case, it is the final step from @{text "\<sigma>\<^bsub>(n-1)\<^esub>"} to @{term \<sigma>\<^sub>n}.\<close>
lemma visible_exec_det:
  "M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> link_wf M M' \<Longrightarrow> M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow> \<sigma>'' = \<sigma>'"
  by (auto simp: visible_exec_det_aux)

text \<open>The lemma @{term exec_det} below asserts that the execution of the languages is deterministic.
The proof is by structural induction on the definition of @{term exec}.\<close>
lemma exec_det: 
  "M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow> \<sigma>'' = \<sigma>'"
  by (auto simp: exec_det_aux)

text\<open>We make the proof details of the determinism of language and visible-states at the lemma @{term exec_det_aux} 
and lemma @{term visible_exec_det_aux}, respectively, in Appendix \ref{Deterministic_appendix}.\<close>
subsection\<open>Linking modules preserving execution \label{linking_preserve_exe}\<close>
text\<open>
Intuitively, taking a module @{term M} and placing it in a larger context @{term M'} 
cannot reduce the behaviors of @{term M}. 
Therefore, if @{term M} can perform some execution step on its own, 
we would expect it also to perform that same step when linked against an arbitrary module @{term M'}. 
We formally prove this below. 

A similar argument also applies to the visible state semantics. 
If @{term M} when linked against @{term M'} has a visible execution, 
 it should still have that same execution when linked against @{term "(M' \<circ>\<^bsub>l\<^esub> M'')"}. 
We formally prove this property also.

Together these properties tell us that linking is monotonic for
a module's executions (i.e., increasing the context increases the possible executions 
but does not remove any), as should be expected.\<close>

text\<open>In this section, we place proofs of module linking preserving execution.
First, we need to define @{term link_wf_3M} for three modules whose domains are pairwise disjoint.\<close>

definition 
link_wf_3M :: "Module \<Rightarrow> Module \<Rightarrow> Module \<Rightarrow> bool"
  where
"link_wf_3M M M' M'' \<equiv> ((dom M \<inter> dom M' = {}) \<and> 
                       (dom M' \<inter> dom M'' = {}) \<and>  
                        (dom M'' \<inter> dom M = {}))"

text \<open>
Technical lemma @{term link_dom} says that 
the union of two domains of two modules @{term M} and @{term M'} is the two's union domain. \<close>

lemma link_dom [simp]: 
  "dom (M \<circ>\<^bsub>l\<^esub> M') = dom M \<union> dom M'"
  by (auto simp: moduleLinking_def moduleAux_def dom_def)

text \<open>We also need technical lemma @{term link_wf_3M_dest}, saying that 
if three modules whose domains are pairwise disjoint are well-formed, 
pair arbitrary modules are also well-formed. \<close>
  
lemma link_wf_3M_dest [simp,intro,dest]: 
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf M M'"
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf M' M''"
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf M M''"
      "link_wf_3M M M' M'' \<Longrightarrow> link_wf (M \<circ>\<^bsub>l\<^esub> M') M''"
  by(fastforce simp: link_wf_def link_wf_3M_def)+
end