import markdownIt from 'markdown-it';
const md = markdownIt();
export const markdownify = (content) => md.renderInline(content);

export const unmarkdownify = (content) => {
  return md
    .parseInline(content)[0]
    .children.filter(
      (token) => token.type === 'text' || token.type === 'code_inline'
    )
    .map((token) => token.content)
    .join('');
};
