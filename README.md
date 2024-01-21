## Description
Phoebe is a epistemic model checker for privacy properties in security protocols. 

### Features
* Phoebe implements a symbolic model of security protocols: messages are expressed as algebraic terms (not bitstrings) and a Dolev-Yao attacker is assumed 
* Phoebe works for protocols with bounded number of sessions.
* Phoebe assume a limited Dolev-Yao attacker: the DY attacker can only swap well typed terms
* Privacy properties are expressed with an Epistemic Logic Language
* Protocols are modelled using a Send/Receive language
* The user input: 
  - the protocol description
  - an epistemic formula expressing the desired property
  - the domains for protocol names, and long-term keys if necessary
  - the maximum number of sessions
* The protocol model in Phoebe is an Interpreted System


## Examples
* Private Authentication Protocol (By Abadi) 
* Basic Hash Protocol
* Tag-Reader protocol (Example 17 in Hirschi et al.) 

## Installation

You should have Haskell installed. Phoebe was tested with The Glorious Glasgow Haskell Compilation System, version 9.2.4.
Compatibility with other versions is unknown.

## Usage 


### With GHCI
This is the easiest way to get the results, although not the most performant.
First start ghci

    $ ghci

then, load each example module.

Example with PrivAuth

    > :l PrivAuth.hs
    > sat privAuthX (Neg goal3)
      Just [1.(a,A,1,{kb})!: (n1){⟨a,n1⟩}_b
      ,1.(a,C,1,{kb})?: (b,n2,a){⟨b,n2⟩}_a
      ,2.(a,C,1,{kb})!: (n3){⟨a,n2,n3⟩}_b
      ]

Example with Basic Hash Protocol

    > :l BasicHash.hs
    > satNegStrongUnlinkabilityBH
      Just [1.(t1,T,1,{})!: (n1)⟨n1,hash(⟨n1,k1⟩)⟩
      ,1.(t1,T,2,{})!: (n2)⟨n2,hash(⟨n2,k1⟩)⟩
      ,1.(t1,T,3,{})!: (n3)⟨n3,hash(⟨n3,k1⟩)⟩
      ] 


Example with the Tag Reader Protocol TR

    > satKeyLinkTR
      Just [1.(t1,T,1,{})!: (n1)⦃n1⦄_k1
      ,1.(t2,T,2,{})!: (n2)⦃n2⦄_k1
      ,1.(r1,R,1,{k1,k2})?: ()⦃n1⦄_k1
      ,2.(r1,R,1,{k1,k2})!: (n3)⦃n3⦄_k1
      ,2.(t1,T,1,{})?: ()⦃n2⦄_k1
      ,2.(t2,T,2,{})?: ()⦃n1⦄_k1
      ,3.(t1,T,1,{})!: ()⦃⟨n2,n1⟩⦄_k1
      ,3.(t2,T,2,{})!: ()⦃⟨n1,n2⟩⦄_k1
      ]

### Compiling the code
This approach gives better performance result.
First compile the main module naming the executable `phoebe`.

    $ ghc Main.hs -o phoebe

Then run phoebe with one of the argument specified in Main.hs and corresponding 
to one of the Model Checking examples of the three studied protocols.

For example the following will check for the strong unlinkability for the Basic Hash protocol.

    $ time ./phoebe A 

### Limitations

- To specify the number of sessions, the domain $D$, the user
needs to change the specific Example file, then reinterpret/recompile the code.
(TODO) We will refactor the code to make them command line arguments.
- All phoebe formulas and protocol descriptions in the example files
are written with Haskell data constructors. 
(TODO) We will write parsers to have more user-friendly syntax.
- To implement another example, the user also need to explicitly construct 
the agents, see one of the current examples on how it's done. (TODO) This will be
automated in the future.
