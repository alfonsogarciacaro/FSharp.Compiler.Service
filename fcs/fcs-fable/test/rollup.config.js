import fable from 'rollup-plugin-fable';
const fableUtils = require("fable-utils");

// const babelOptions = fableUtils.resolveBabelOptions({
//   presets: [["env", {"modules": false}]]
// });

const fableOptions = {
  //babel: babelOptions,
  //plugins: [],
  define: [
    "FX_NO_CORHOST_SIGNER",
    "FX_NO_LINKEDRESOURCES",
    "FX_NO_PDB_READER",
    "FX_NO_PDB_WRITER",
    "FX_NO_WEAKTABLE",
    "FX_REDUCED_EXCEPTIONS",
    "NO_COMPILER_BACKEND",
    "NO_EXTENSIONTYPING",
    "NO_INLINE_IL_PARSER"
  ]
};

export default {
  input: './fcs-fable-test.fsproj',
  output: {
    file: './out/bundle.js',
    format: 'cjs', // 'amd', 'cjs', 'es', 'iife', 'umd'
  },
  plugins: [
    fable(fableOptions),
  ],
};
