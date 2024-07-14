0. Remove all previous coq installation to avoid conflicts, check if coq is no longer available by `coqc --version` 
1. Install [coq](coq.inria.fr). See more [here](https://coq.inria.fr/opam-using.html)
1.1. Install [opam](https://opam.ocaml.org/doc/Install.html) globally if possible
- `bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"`
- check it by `opam --version`
- be sure that you have `git` and `make` installed
- run `opam init`, allow it to modify shell init script - that may take a while
- `eval $(opam env --switch=default)` to update environment, follow other recommendation if any (dependent on system)
1.2. Create so called switch in opam to locally install Coq of certain version (update environment every time after opam command finished by `eval $(opam env)`)
- `opam switch create coq-8.16 4.12.0` - that may take a while
- check it by `opam switch list`
- install coq by `opam pin add coq 8.16.1` - we use Coq version 8.16.1, follow recommendations if any (it can require system wide packages not supported by opam, then they should be installed manually, usually opam gives verbose output)
- check the installation by `coqc --version`
2. Install [VS Code](https://code.visualstudio.com/)
3. Install [Coq extension](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1)
4. Install [Math Unicode extension](https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode)
5. Try to open any *.v file from this repo to see syntax highlighting and possibility to evaluate expressions forth and back (the hot keys are described on the Coq extension page from 3)



