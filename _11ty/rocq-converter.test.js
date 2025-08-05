import assert from 'assert';
import { rocqToMd } from './rocq-converter.js';

const testCases = [
  {
    name: 'Empty array',
    input: [],
    expected: '',
  },
  {
    name: 'Only code',
    input: ['Definition a := 1.', 'Print a.'],
    expected: '```coq\nDefinition a := 1.\nPrint a.\n```',
  },
  {
    name: 'Only markdown',
    input: ['(*@@ # Title *)', '(*@@ ## Subtitle *)'],
    expected: '# Title\n## Subtitle',
  },
  {
    name: 'Mixed content',
    input: [
      '(*@@ # Title *)',
      'Definition a := 1.',
      '(*@@ ## Subtitle *)',
      'Print a.',
    ],
    expected:
      '# Title\n```coq\nDefinition a := 1.\n```\n## Subtitle\n```coq\nPrint a.\n```',
  },
  {
    name: 'Code block at the end',
    input: ['(*@@ # Title *)', 'Definition a := 1.'],
    expected: '# Title\n```coq\nDefinition a := 1.\n```',
  },
  {
    name: 'Markdown at the end',
    input: ['Definition a := 1.', '(*@@ # Title *)'],
    expected: '```coq\nDefinition a := 1.\n```\n# Title',
  },
];

testCases.forEach(({ name, input, expected }) => {
  const result = rocqToMd(input);
  assert.strictEqual(result, expected, `Test failed: ${name}`);
});

console.log('All rocq-converter tests passed!');
