export function parseCoqContent(coqContent) {
  if (!coqContent) {
    return [];
  }

  const sentences = [];
  let currentSentence = '';
  let commentDepth = 0;

  for (let i = 0; i < coqContent.length; i++) {
    if (coqContent.startsWith('(*', i)) {
      if (commentDepth === 0) {
        if (currentSentence !== '')
            sentences.push(currentSentence);
        currentSentence = '';
      }
      currentSentence += '(*';
      commentDepth++;
      i++; // Skip the next character
    } else if (coqContent.startsWith('*)', i)) {
      i++; // Skip the next character
      currentSentence += '*)';
      commentDepth--;
      if (commentDepth === 0) {
        sentences.push(currentSentence);
        currentSentence = '';
      }
    } else if (commentDepth === 0 && coqContent[i] === '.') {
      currentSentence += '.';
      sentences.push(currentSentence);
      currentSentence = '';
    } else {
      currentSentence += coqContent[i];
    }
  }

  if (currentSentence !== '')
    sentences.push(currentSentence);

  return sentences;
}
