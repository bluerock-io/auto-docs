import assert from 'assert';
import { parseCoqContent } from './coq-parser.js';

const testCases = [
  {
    name: 'Empty string',
    input: '',
    expected: [],
  },
  {
    name: 'No comments',
    input: 'Definition a := 1.',
    expected: ['Definition a := 1.'],
  },
  {
    name: 'Single comment',
    input: '(* a comment *)',
    expected: ['(* a comment *)'],
  },
  {
    name: 'Comment at the beginning',
    input: '(* a comment *) Definition a := 1.',
    expected: ['(* a comment *)',' Definition a := 1.'],
  },
  {
    name: 'Comment at the end',
    input: 'Definition a := 1. (* a comment *)',
    expected: ['Definition a := 1.', ' ', '(* a comment *)'],
  },
  {
    name: 'Empty comment',
    input: '(*||*)',
    expected: ['(*||*)'],
  },
  {
    name: 'Comment in the middle',
    input: 'Definition a (* a comment *) := 1.',
    expected: ['Definition a ', '(* a comment *)', ' := 1.'],
  },
  {
    name: 'Multiple comments',
    input: '(*c1*)def a(*c2*).(*c3*)',
    expected: ['(*c1*)', 'def a', '(*c2*)', '.', '(*c3*)'],
  },
  {
    name: 'Nested comments',
    input: 'def a (* nested (* comment *) here *) end.',
    expected: ['def a ', '(* nested (* comment *) here *)', ' end.'],
  },
  {
    name: 'Adjacent comments',
    input: 'def a (*c1*) (*c2*) end.',
    expected: ['def a ', '(*c1*)',' ', '(*c2*)', ' end.'],
  },
  {
    name: 'Complex example',
    input:
      "Require Import Lia. (* solve arith problems *)\nTheorem plus_comm: forall n m: nat, n + m = m + n.\nProof.\n  intros n m. (* introduce variables *)\n  induction n as [|n' IHn'].\n  - simpl. rewrite <- plus_n_O. reflexivity.\n  - simpl. rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.\nQed. (* we are done *)",
    expected: [
    'Require Import Lia.',
    ' ',
    '(* solve arith problems *)',
    '\nTheorem plus_comm: forall n m: nat, n + m = m + n.',
    '\nProof.',
    '\n  intros n m.',
    ' ',
    '(* introduce variables *)',
    "\n  induction n as [|n' IHn'].",
    '\n  - simpl.',
    ' rewrite <- plus_n_O.',
    ' reflexivity.',
    '\n  - simpl.',
    ' rewrite <- plus_n_Sm.',
    " rewrite IHn'.",
    ' reflexivity.',
    '\nQed.',
    ' ',
    '(* we are done *)',
    ],
  },
];

testCases.forEach(({ name, input, expected }) => {
  const result = parseCoqContent(input);
  assert.deepStrictEqual(result, expected, `Test failed: ${name}`);
});

console.log('All tests passed!');
