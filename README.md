# Formal Verification for Q#

This repository contains Q* (pronounced Q-star), a tool for formally verifying quantum programs written in [Q#](https://docs.microsoft.com/en-us/azure/quantum/overview-what-is-qsharp-and-qdk).
It is implemented as a library for [F*](https://www.fstar-lang.org/) and is currently in the prototype stage of development.
Its goal is to allow Q# developers to formally reason about their programs, providing stronger correctness guarantees than testing and leading to higher-quality Q# code.

**NOTE**: The `sep-logic` branch contains preliminary work building Q* on top of [Steel](https://dl.acm.org/doi/abs/10.1145/3473590), a language for verifying concurrent programs that is built on top of F*'s concurrent separation logic, SteelCore. In this branch, you can ignore the `examples` and `qstar/translator` directories. Only the code in `qstar/src` is relevant.

## Directory

- [`qstar/examples`](qstar/examples): Examples and demos of using Q* and the Q#-to-Q* translator.
- [`qstar/src`](qstar/src): Q* library code, written in F*. See the [README](qstar/src/README.md) in that directory for more information.
- [`qstar/translator`](qstar/translator): Plugin for the Q# compiler to automatically translate Q# programs into Q* instructions.

## Requirements

Install [F*](https://www.fstar-lang.org/) and [.NET](https://dotnet.microsoft.com/en-us/download).

If building F* from source, we recommend using the `everest` script from [Project Everest](https://github.com/project-everest/everest):

```
./everest check
./everest FStar make
```

## Demo

You can convert the [Examples.qs](qstar/examples/Examples.qs) file into Q\* instruction trees by running `dotnet build` from the `qstar/examples` directory.
This will produce an F* file in `qstar/examples/obj/QStar`.
A prettified excerpt from the output is in [Demo.fst](qstar/examples/Demo.fst).
You should be able to typecheck this file in F* (e.g., by copying it into the `qstar/src` directory and running `make`), indicating that our Q# definitions satisfy basic well-formedness properties.
Proofs about the semantics of the example programs are in [DemoProofs.fst](qstar/examples/DemoProofs.fst).

## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft 
trademarks or logos is subject to and must follow 
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/en-us/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.
