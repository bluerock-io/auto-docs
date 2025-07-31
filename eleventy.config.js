import { mvParser } from './_11ty/mv-parser.js';
import { parseCoqContent } from './_11ty/coq-parser.js';
import { rocqToMd } from './_11ty/rocq-converter.js';
import slugify from "@sindresorhus/slugify"; /* same as 11ty */

import syntaxHighlight from "@11ty/eleventy-plugin-syntaxhighlight";

export default function (eleventyConfig) {
  eleventyConfig.addPlugin(syntaxHighlight);
  eleventyConfig.addGlobalData("siteTitle", "BlueRock FM Docs");
  eleventyConfig.addTemplateFormats("v");
  eleventyConfig.addPreprocessor("markdown-rocq", "v", (data, content) => {
      const sentences = parseCoqContent(content);
      const markdownOutput = rocqToMd(sentences);
      return markdownOutput;
  });
    eleventyConfig.addExtension("v", {
		key: "md",
	});

    eleventyConfig.addCollection("learn", function(collectionApi) {
        return collectionApi.getFilteredByTag("learn");
    });

    eleventyConfig.addCollection("reference", function(collectionApi) {
        return collectionApi.getFilteredByTag("doc");
    });

    eleventyConfig.addCollection("where", function(collectionApi) {
        const allProvides = collectionApi.getAll().flatMap(item => item.data.provides || []);
        return [...new Set(allProvides)];
    });

    eleventyConfig.addFilter("terminology", (value) => {
        // Extend this to add a link to a canonical article if one exists.
        if (false) {
            return `<a href="/where/${slugify(value)}">${value}</a>`;
        } else {
            return value;
        }
    });

    eleventyConfig.addPassthroughCopy({'node_modules/lunr/lunr.min.js': 'node_modules/lunr/lunr.min.js'});
    eleventyConfig.addPassthroughCopy('content/**/*.v', {
        mode: "html-relative"
    });

    // eleventyConfig.addExtension("v", {
    //     compile: async (inputContent)  => {
    //         const sentences = parseCoqContent(inputContent);
    //         const markdownOutput = rocqToMd(sentences);
    //         return async () => {
    //             return markdownOutput;
    //         };
    //     }
    // });

	//   eleventyConfig.addCollection("allContentPages", function(collectionApi) {
  //   return collectionApi.getAll().filter(item => {
  //     // Filter out index pages and ensure it's a content file
  //     return item.inputPath.startsWith('./content/') &&
  //            !item.inputPath.includes('index.') &&
  //            (item.inputPath.endsWith('.md') || item.inputPath.endsWith('.html') || item.inputPath.endsWith('.v'));
  //   }).sort((a, b) => a.data.title.localeCompare(b.data.title)); // Sort by title
  // });
}
export const config = {
    dir: {
	      input: 'content',
	      output: '_site',
        includes: '../_includes',
    }
};
