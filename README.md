# ARGES
Advanced Renormalisation Group Equation Simplifier.

When using ARGES, please cite the publication [arXiv:2012.12955](https://arxiv.org/abs/2012.12955), which also contains installation instructions as well as short introduction with examples.

The package consists of a standalone Wolfram Language file `ARGES.m`, which can be obtained from [this repository](https://github.com/TomSteu/ARGES).
It can be loaded to a running kernel by invoking
```
Get["/path/to/ARGES.m", ARGES`];
```
or for convenience moved to a location contained in `$Path`, in which case it is included via
```
<< ARGES`
```
If no output is produced by the method of choice, the package is initialised correctly and can be used. Check the [publication](https://arxiv.org/abs/2012.12955) to get started.

Note that the main repository has been migrated to [gitlab](https://gitlab.com/tomsteu/arges).
