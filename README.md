# Translator from HOL Zero / Common HOL to Metamath Zero

This is work in progress. The goal is to be able to verify and translate Common HOL proofs,
in particular [flyspeck](http://www.proof-technologies.com/flyspeck/replaying.html), into a
[MM0](https://github.com/digama0/mm0) proof.

To run this tool on flyspeck, first download all the `.tgz` files and unpack them into directories like `flyspeck/BaseSystem/`, `flyspeck/Multivariate/`, etc.; then run `hz-to-mm0 < `[`flyspeck.txt`](flyspeck.txt), after modifying the `set-cwd` line to point to your `flyspeck` directory (or running `hz-to-mm0` from the `flyspeck` directory).