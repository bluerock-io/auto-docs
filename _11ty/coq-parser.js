export function parseCoqContent(coqContent) {
    if (!coqContent) {
        return [];
    }

    const sentences = [];
    let currentSentence = '';
    let commentDepth = 0;

    for (let i = 0; i < coqContent.length; i++) {
        if (coqContent.startsWith('(*', i)) {
            if (commentDepth === 0 && currentSentence.trim() !== '') {
                sentences.push(currentSentence.trim());
                currentSentence = '';
            }
            currentSentence += '(*';
            commentDepth++;
            i++; // Skip the next character
        } else if (coqContent.startsWith('*)', i)) {
            currentSentence += '*)';
            commentDepth--;
            if (commentDepth === 0) {
                sentences.push(currentSentence.trim());
                currentSentence = '';
            }
            i++; // Skip the next character
        } else if (commentDepth === 0 && coqContent[i] === '.' && (i == coqContent.length || coqContent[i+1].match(/\s/))) {
            currentSentence += '.';
            sentences.push(currentSentence);
            if (i < coqContent.length) {
              currentSentence = coqContent[i+1];
              i++;
            } else {
              currentSentence = '';
            }
        } else {
            currentSentence += coqContent[i];
        }
    }

    if (currentSentence.trim() !== '') {
        sentences.push(currentSentence.trim());
    }

    return sentences;
}
