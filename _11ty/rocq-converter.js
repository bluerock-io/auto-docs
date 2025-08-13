export function rocqToMd(sentences) {
  if (!sentences || sentences.length === 0) {
    return '';
  }
  let markdown = '';
  let codeBlock = '';
  function flushCodeBlock() {
    if (codeBlock.trim() !== '') {
      // Remove leading and trailing newlines.
      codeBlock = codeBlock.replace(/^[\r\n]+/g, '').replace(/[\r\n]+$/g, '');

      // Escape to protect from cpp:{{ ... }}.
      // see https://liquidjs.com/tutorials/escaping.html#Liquid-Escape.
      markdown +=
          '{% raw %}\n```coq\n' + codeBlock.replace(/^(\s*\n)+/,'').trimEnd() + '\n```\n{% endraw %}\n';

      codeBlock = '';
    }
  }
  let hide = false;
  for (const sentence of sentences) {
    if (sentence === '(*@END-HIDE@*)') {
      hide = false;
      continue;
    }
    if (hide) continue;
    if (sentence === '(*@HIDE@*)') {
      hide = true;
    } else if (sentence.startsWith('(*|')) {
        if (!sentence.endsWith('|*)')) {
            console.log(`Bad comment:\n"${sentence}"`);
        }
      flushCodeBlock();
      const content = sentence.substring(3, sentence.length - 3).trim();
      markdown += content + '\n';
    } else {
      codeBlock += sentence;
    }
  }
  flushCodeBlock();
  return markdown.trim();
}
