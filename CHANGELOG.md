# 0.0.1
* Define `Adj.Algebra` module
* Define `Adj.Program` module
* Define `Adj.Algebra.Semigroupoid` module
* Define `Adj.Algebra.Category` module
* Define `Adj.Algebra.Functor` module
* Define `Adj.Algebra.Morphism` module
* Define `Adj.Algebra.Morphism.Flat` module
* Define `Adj.Algebra.Morphism.Dual` module
* Define `(-->)` type alias
* Define `(<--)` type alias
* Define `Adj.Algebra.Morphism.Kleisli` module
* Define `(-/->)` type alias
* Define `(<-\-)` type alias
* Define `Adj.Algebra.Product` module
* Define `Adj.Algebra.Sum` module
* Define `Adj.Algebra.Initial` module
* Define `Adj.Algebra.Terminal` module

# 0.0.2
* Define `Adj.Algebra.Unit` module
* Define `Adj.Program.Instruction` module
* Define `Adj.Program.Construction` module
* Define `:.` method in `Categroy` typeclass
* Define `Adj.Program.Option` module
* Define `Covariant` type family
* Define `Contravariant` type family
* Move `Semigroupoid` module content to `Category`
* Move `Morphism` module content to `Category`
* Move `Functor` module content to `Category`
* Move `Product` module content to `Category`
* Move `Sum` module content to `Category`
* Move `Terminal` module content to `Category`
* Move `Initial` module content to `Category`
* Move `Unit` module content to `Category`

# 0.0.3
* Make `Unit` type family closed
* Define `Adj.Program.Disbandable` module
* Define `:.` method in `Categroy` typeclass
* Define `Adj.Program.Option` module
* Define `Covariant` type family
* Define `Contravariant` type family
* Move `Semigroupoid` module content to `Category`
* Move `Morphism` module content to `Category`
* Move `Functor` module content to `Category`
* Move `Product` module content to `Category`
* Move `Sum` module content to `Category`
* Move `Terminal` module content to `Category`
* Move `Initial` module content to `Category`
* Move `Unit` module content to `Category`

# 0.0.4
* Make `Unit` type family closed
* Define `-=-` and `=-=` operators in `Disbandable` typeclass
* Define `|->` operator in `Adj.Algebra.Category` module
* Define `Betwixt` type family in `Adj.Algebara.Category` module
* Define `|-|->` operator in `Adj.Algebra.Category` module
* Define `|-|-|->` operator in `Adj.Algebra.Category` module
* Define `-|` operator in `Functor` typeclass
* Define `-|-|` operator in `Functor` typeclass
* Define `-|-|-|` operator in `Functor` typeclass
* Rename `Disbandable` typeclass and module to `Casting`
* Define `Adj.Auxiliary` module
* Move `Casting` typeclass to `Adj.Auxiliary` method
* Define `Tensor` morpism
* Define `Component` typeclass
* Define `Transformation` typeclass
* Define `Semimonoidal` type family
* Rename `Option` constructor to `This`
* Rename `Adoption` constructor to `That`

# 0.0.5
* Define `-*~*->` type alias
* Define `-+~*->` type alias
* Define `-*~+->` type alias
* Define `-+~+->` type alias
* Define `:*:.` type alias
* Define `:+:.` type alias
* Define `.:*:` type alias
* Define `.:+:` type alias
* Define `Adj.Program.Progress` module
* Define `Day` convolution
* Remove `Tensor` morphism
* Change `Semimonoidal` type family definition
* Define `Identity` datatype
* Define `Monoidal` type family
* Define `TU` scheme
* Define `Adjunction` type family
* Define `Bindable` type family
* Define `Traversable` type family
* Define `|-/->` operator
* Define `|-|-/->` operator
* Define `Adj.Program.Generation` module
* Remove `Adj.Program.Construction` module
* Remove `Adj.Program.Instruction` module
* Define `Construction` type alias of `Generation`
* Define `Instruction` type alias of `Generation`

# 0.0.6
* Change `Semimonoidal` type family definition
* Change `Monoidal` type family definition
* Define `point` method
* Change `TU` datatype definition
* Define `Variance` datatype
* Change `Casting` typeclass definition
* Define `extract` method
* Define `absurd` method
* Define `empty` method
* Define `boring` method
* Define `=-=` operator
* Define `|.:|` type alias of `FG`
* Rename `TU` scheme to `FG`
* Define `FGF` scheme
* Define `..:` operator
* Define `...:` operator
* Define `....:` operator
* Define `.....:` operator
* Define `......:` operator
* Define `.......:` operator
* Define `........:` operator
* Define `|.:.|` type alias of `FGF` of `FGF`
* Define `..:` type operator
* Define `...:` type operator
* Define `....:` type operator
* Define `.....:` type operator
* Define `......:` type operator
* Define `.......:` type operator
* Define `........:` type operator
* Define `-=-` operator

# 0.0.7
* Define `Adj.Program.Datastructure` module
* Define `Adj.Program.Datastructure.Implementation` module
* Define `Adj.Program.Datastructure.Implementation.List` module
* Define `List` type alias
* Rename `-|` operator to `-|-`
* Rename `-|-|` operator to `-||-`
* Rename `-|-|-|` operator to `-|||-`
* Define `-|--` operator
* Define `--|--` operator
* Define `-||--` operator
* Define `-|||--` operator
* Define `--||--` operator
* Define `--|||--` operator
* Rename `|.:|` type alias to `=!?=`
* Rename `|.:.|` type alias to `=!?!=`
* Define `Adj.Program.Controlflow` module
* Define `Adj.Program.Controlflow.Implementation` module
* Define `Adj.Program.Controlflow.Implementation.State` module
* Define `State` type alias
* Define `FFGH` scheme
* Define `=!!??` type alias of `FFGH`
* Define `=--` operator
* Define `=---` operator
* Define `=----` operator

# 0.0.8
* Change `Generation` definition
* Define `||` union constraint type from @rampion's package
* Remove `.:+:` type alias
* Define `:+:>` type alias
* Remove `:+:.` type alias
* Define `<:+:` type alias
* Remove `.:*:` type alias
* Define `:*:>` type alias
* Remove `:*:.` type alias
* Define `<:*:` type alias
* Rename `Option` module and type to `Maybe`
* Change `Maybe` type definition
* Change `Progress` type definition
* Define `current` method
* Define `modify` method
* Define `Adj.Program.Controlflow.Implementation.Optics` module
* Change `State` type definition
* Define `Lens` type
* Define `view` method
* Define `Prism` type
* Define `review` method

# 0.0.9
* Define `Adj.Program.Primitive` module
* Move `Adj.Program.Maybe` to `Adj.Program.Primitive` module
* Move `Adj.Program.Progress` to `Adj.Program.Primitive` module
* Move `Adj.Program.Generation` to `Adj.Program.Primitive` module
* Define `Adj.Program.Primitive.Boolean` module
* Define `Adj.Algebra.Set` module
* Move `:*:` to `Adj.Algebra.Set` module
* Move `:+:` to `Adj.Algebra.Set` module
* Rename `Unit` type family to `Neutral`
* Rename `Initial` datatype to `Void`
* Rename `Terminal` datatype to `Unit`
* Move `Unit` to `Adj.Algebra.Set` module
* Move `Void` to `Adj.Algebra.Set` module
* Move `absurd` to `Adj.Algebra.Set` module
* Move `boring` to `Adj.Algebra.Set` module
* Define `Setoid` typeclass
* Define `Semigroup` typeclass
* Define `Monoid` typeclass
* Define `Group` typeclass
* Define `Ringoid` typeclass
* Define `Quasiring` typeclass
* Define `Structural` wrapper for deriving
* Define `=:*:=` type alias
* Define `=:+:=` type alias
* Define `FGG` scheme
* Define `Adj.Program.Datastructure.Implementation.Tree` module

# 0.1.0
* Define `Construct` pattern
* Define `Instruct` pattern
* Define `Load` pattern
* Change `Functor` typeclass definition
* Replace `Primary` associated type family with `Casted` open type family
* Define `-/|/->` operator
* Define `-//|//->` operator
* Rename `|->` operator to `-|->`
* Rename `|-|->` operator to `-||->`
* Rename `|-|-|->` operator to `-|||->`
* Rename `|-/->` operator to `-|/->`
* Rename `|-|-/->` operator to `-||/->`
* Remove `-/->` type operator
* Remove `<-\-` type operator
* Define `-|-<` operator
* Change `Betwixt` type family definition

# 0.1.1
* Remove `Betwixt` type famyly
* Rename `-|->` operator to `->-` and flip arguments
* Define `-><-` operator
* Change `Covariant` type family definition
* Change `Contravariant` type family definition
* Define `OP` type family
* Define `Functoriality` datatype
* Rename `-|-<` operator to `-<-` and flip arguments
* Define `-<>-` operator
* Rename `-||->` operator to `->>-` and flip arguments
* Define `-<<-` operator
* Rename `-|||->` operator to `->>>-` and flip arguments
* Define `-->--` operator
* Define `->--` operator
* Define `->>--` operator
* Define `-->>--` operator
* Rename `-/|/->` operator to `-/>/-`

# 0.1.2
* Rename `-|/->` operator to `-/>-` and flip arguments
* Rename `-||/->` operator to `-/>>-` and flip arguments
* Define `--/>>/--` operator
* Define `-/>>/--` operator
* Define `-/->` type operator
* Define `<-\-` type operator
* Define `--/>/--` operator
* Define `-/>/--` operator
* Change `Semimonoidal` type family definition
