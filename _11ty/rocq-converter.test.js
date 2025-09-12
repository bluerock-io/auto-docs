import assert from 'assert';
import { rocqToMd } from './rocq-converter.js';

const testCases = [
  {
    name: 'Empty array',
    input: [],
    expected: '',
  },
  {
    name: 'Only hide',
    input: ['(*@HIDE@*)','\n','foo','(*@END-HIDE@*)'],
    expected: '',
  },
  {
    name: 'Only code',
    input: ['Definition a := 1.', '\nPrint a.'],
      expected: '{% raw %}\n```coq\nDefinition a := 1.\nPrint a.\n```\n{% endraw %}',
  },
  {
    name: 'Only markdown',
    input: ['(*| # Title |*)', '(*| ## Subtitle |*)'],
    expected: '# Title\n## Subtitle',
  },
  {
    name: 'Mixed content',
    input: [
      '(*| # Title |*)',
      'Definition a := 1.',
      '(*| ## Subtitle |*)',
      'Print a.',
    ],
    expected:
      '# Title\n{% raw %}\n```coq\nDefinition a := 1.\n```\n{% endraw %}\n## Subtitle\n{% raw %}\n```coq\nPrint a.\n```\n{% endraw %}',
  },
  {
    name: 'Code block at the end',
    input: ['(*| # Title |*)', 'Definition a := 1.'],
    expected: '# Title\n{% raw %}\n```coq\nDefinition a := 1.\n```\n{% endraw %}',
  },
  {
    name: 'Markdown at the end',
    input: ['Definition a := 1.', '(*| # Title |*)'],
    expected: '{% raw %}\n```coq\nDefinition a := 1.\n```\n{% endraw %}\n# Title',
  },
];

testCases.forEach(({ name, input, expected }) => {
  const result = rocqToMd(input);
  assert.strictEqual(result, expected, `Test failed: ${name}`);
});

console.log('All rocq-converter tests passed!');
