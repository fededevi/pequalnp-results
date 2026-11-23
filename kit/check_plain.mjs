// usage: node check_plain.mjs <outside-guard.mjs> <lean file> [allowed module ...]
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
const [guard, file, ...allowed] = process.argv.slice(2);
const { checkImports } = await import(pathToFileURL(guard).href);
try {
  const seen = checkImports(readFileSync(file), allowed.length ? allowed : ['PEqualNP.Defs']);
  console.log('PLAIN OK, imports: ' + seen.join(' '));
} catch (e) { console.log('REFUSED: ' + e.message); process.exit(1); }
