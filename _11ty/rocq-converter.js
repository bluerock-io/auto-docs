export function rocqToMd(sentences) {
  if (!sentences || sentences.length === 0) {
    return '';
  }
  let markdown = '';
  let codeBlock = '';
  function flushCodeBlock() {
    if (codeBlock.trim() !== '') {
        markdown += '```coq\n' + codeBlock.replace(/^[\r\n]+/g, '').replace(/[\r\n]+$/g, '') + '\n```\n';
      codeBlock = '';
    }
  }
  for (const sentence of sentences) {
    if (sentence.startsWith('(*@@')) {
      flushCodeBlock();
      const content = sentence.substring(4, sentence.length - 2).trim();
      markdown += content + '\n';
    } else {
      codeBlock += sentence;
    }
  }
  flushCodeBlock();
    console.log(markdown);
  return markdown.trim();
}
