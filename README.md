# Foundations for reasoning about Holistic Specifications

This repository contains the theory of holistic specifications in Isabelle/HOL, which was developed as part of my [Master's thesis](https://ducthan.net/assets/pub/MPhilThesis.pdf) in 2020 at the University of Melbourne.

* Specifications of sufficient conditions may be enough for reasoning about complete and unchanging programs of a closed system. However, in an open world, there is not a luxury of trusting external components of possibly unknown provenance, buggy, or potentially malicious. It is critical to ensure that our components are robust when they collaborate with a wide range of external components. 
Holistic specifications which are concerned with sufficient, as well as with necessary conditions could make programs more robust in an open-world setting.

* The theory of holistic specifications and several proofs is comprising about 2,000 lines of code of definitions and proofs in Isabelle/HOL. 

* To develop holistic specifications, there is a need of having an underlying programming language. It is based on an object-oriented programming language with modules as repositories of code, classes with fields, methods, objects, a way to link modules into others, and a concept of program execution. 

## Repository contents

 * [`Language.thy`](Language.thy): 
 
 	* A language, called Loo, a minimal such object-oriented language. The Loo programs consist of modules, which are repositories of code designing as classes and modules. The class definition consists of field and method definition. Method body consists of a sequence of statements. These are field read, field assignment, method call, object creation, and return statement. 
 	* An operational semantics of the language Loo. We start by defining the runtime entities, and runtime configurations, which consist of heaps and stacks of frames. The code to be executed is kept as a part of the runtime configuration. Then, we define one-module execution through a judgment of the form M, σ ~> σ′ where M is a module and σ, σ′ are runtime configurations.
    * Module linking. A module linking is a concept of linking other modules to the module under consideration. Namely, it is an operator holding a union of the two modules, and their domains of these modules are disjoint.
    * Module pairs and visible states semantics. Module pairs are an internal module adheres to an invariant assertion, and another module called the external module.
    * Proofs - Execution in Loo and visible states is deterministic. That means a language is deterministic if any two executions of the same command from the same initial state will always arrive in the same final state.
    * Proofs - Properties of Linking. The linking is associative and commutative and preserves both one-module and two-module execution.
    
 * [`Adaptation.thy`](Adaptation.thy): 
    * Adaptation on runtime configurations. Adaptation returns a new configuration whose stack has the top frame as taken from the current configuration, while the heap is taken from the second configuration.

 * [`Logic.thy`](Logic.thy): 
    * Basic Assertions and Assertions with Logical connectives and quantifiers.
        * Basic assertions. Some assertions involving expressions which express the relation between the validity of assertions and the values of expressions are defined.
        * Assertions with logical connectives and quantifiers. Assertions establish some standard logical operators (∧, ∨, →, ¬, ∀ and ∃).
    * Satisfaction of Assertions - Access and Control.
        * Permission. Permission assertion expresses that an object has the potential to call methods on another object and to do so directly, without help from any intermediary object.
        * Control. Control expresses which object is the process of making a function call on another object and with what arguments.
    * Satisfaction of Assertions - Viewpoint and Space.
        * Viewpoint. Viewpoint is whether an object is viewed as belonging to the internal mode; this is determined by the object's class.
        * Restriction of runtime configurations. The restriction operation restricts objects from a configuration to only those from a given set.
        * Space. Thanks to the definition of restriction of runtime configurations, the space assertion is defined talking about asserting that some property holds in a configuration whose objects are restricted to those from a given set.
    * Satisfaction of Assertions - Time.
        * Time assertions. Some temporal modifiers, such as next ⟨A⟩, and will ⟨A⟩ expressing the assertion A holds at the immediate successor execution point, and some future point respectively thanks to carrying a part of an adaptation on runtime configurations.     
    * Modules satisfying assertions. Define the satisfaction of assertions by modules.     
    * Proofs - Assertions are classical. Some lemmas of assertions are related to standard logical operators and quantifiers (∧, ∨, →, ¬, ∀ and ∃).
    * Proofs - Space assertions. Some lemmas supporting for proofs of reasoning capability-policies.     
    
 
 
 
 
