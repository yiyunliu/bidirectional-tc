# bidirectional-tc
A Haskell implementation of the type system described in the paper [Let Arguments Go First](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_10).

This project is purely for learning purposes, since I have never implemented a serious typechecker.

ArgFirst.hs is the old version, which uses the Barendregt convention to prevent accidental capturing. The variables are all named. There are a couple of functions which does some preprocessing to ensure that the names are distinct before entering the inference monad.

ArgFirstB.hs, the newer version, uses the [bound](https://hackage.haskell.org/package/bound) package for the lambdas and foralls. The opening of scopes still follows the Barendregt convention. Overall, I find this approach much more robust than my handwritten one.

I haven't written many tests yet. As of now, church numerals and pairs all typecheck. Instantiantion of a polymorphic function at multiple call sites with different argument types also seem to work. 
