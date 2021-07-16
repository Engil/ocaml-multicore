const { promisify } = require('util');
const exec = promisify(require('child_process').exec)

let diff_cmd = 'git diff --minimal --numstat';
let changed_cmd = 'git diff --name-only HEAD origin/4.12+domains+effects';

async function get_diff(cmd) {
    try {
	const {stdout, stderr} = await exec(cmd);
	console.log({stdout, stderr});
	let res = stdout === "" ? "0\t0\t\0\n" : stdout; // no change in git diff returns nada
	let s = res.replace("\n", "").split("\t");
	console.log(s);
	return(s);
    }
    catch (e) {
	return undefined;
    }
}

async function getChangedFiles () {
    const {stdout, stderr} = await exec(changed_cmd);
    return (stdout.split("\n"));
};

async function main(github, context) {

    var totalScoreTrunk = 0;
    var totalScoreMulticore = 0;

    var message = "🐪 Hello, I am going to check how much this PR gets us closer to trunk. (a lower score = closer to trunk!)\n\n";

    let fetch = await exec('git fetch origin 4.12+domains+effects');
    console.log(fetch);
    let add_trunk = await exec('git remote add ocaml https://github.com/ocaml/ocaml.git');
    console.log(add_trunk);
    let fetch_trunk = await exec('git fetch ocaml trunk');
    console.log(fetch_trunk);

    let changed = await getChangedFiles();
    console.log(changed);

    changed.pop(); // extra \n

    for (const i of changed) {
	// prelude
	message = message.concat(`### ${i}
| Compared to trunk | 4.12+domains+effects | ${github.head_ref} |
|-|-|-|
`);
	let multicoreCmd = diff_cmd.concat(` ocaml/trunk origin/4.12+domains+effects ${i}`);
	let trunkCmd = diff_cmd.concat(` ocaml/trunk ${i}`);
	let fromMulticore = await get_diff(multicoreCmd);
	let fromTrunk = await get_diff(trunkCmd);

	if (fromTrunk != undefined && fromMulticore != undefined) {

	    let trunkAdded = parseInt(fromTrunk[0]);
	    let trunkRemoved = parseInt(fromTrunk[1]);
	    let multicoreAdded = parseInt(fromMulticore[0]);
	    let multicoreRemoved = parseInt(fromMulticore[1]);
	    let trunkScore = trunkAdded + trunkRemoved;
	    let multicoreScore = multicoreAdded + multicoreRemoved;

	    totalScoreTrunk = totalScoreTrunk + trunkScore;
	    totalScoreMulticore = totalScoreMulticore + multicoreScore;

		let table =
`|Added |${multicoreAdded}|${trunkAdded}|
|Removed |${multicoreRemoved}|${trunkRemoved}|
|Score |${multicoreScore}|${trunkScore}|
`;
                let diff = await exec(`git diff HEAD ocaml/trunk -- ${i}`);
                let diff_message = `
<details>
<summary> Diff for %{i} against trunk </summary>
\`\`\`diff
${diff}
\`\`\`
</details>
`;
		console.log(diff_message);
		console.log(table);
	        message = message.concat(table + diff_message);
	}
    }
    message = message.concat(`Total score for the files changed in this PR: ${totalScoreTrunk}
Total score for the files changed in this PR, relative to Multicore: ${totalScoreMulticore}

Evaluation: `);
    if (totalScoreTrunk < totalScoreMulticore)
	message = message.concat("🎉 Soon enough you will turn Multicore OCaml into trunk!");
    else
	message = message.concat("🔎 There is a lot of work to do, look for lines to match to trunk in grassy areas.");

    return await github.issues.createComment({
        issue_number: context.issue.number,
        owner: context.repo.owner,
        repo: context.repo.repo,
        body: message
    })
}

module.exports = ({github, context}) => {
    return main(github, context);
}
