/*
 * 	17-651 | Group Project | Group 9
 *      main model
 */
open Signature
open Invariant
open Privacy
open Content
open Comment
open Publish
open Tag

check UploadCheck for 12 but exactly 2 Nicebook
check RemoveCheck for 12 but exactly 2 Nicebook
check PublishCheck for 12 but exactly 2 Nicebook
check UnpublishCheck for 12 but exactly 2 Nicebook
check AddCommentCheck for 12 but exactly 2 Nicebook
check AddTagCheck for 12 but exactly 2 Nicebook
check RemoveTagCheck for 12 but exactly 2 Nicebook

run runNicebook {
	all n : Nicebook | nicebookInvariant[n]
	some n, n' : Nicebook, c : Content, u : User, p : PrivacyLevel | 
		upload[n, n', u, c, p] and userInvariant[n, u] and contentInvariant[n, c] and 
		nicebookInvariant[n] and nicebookInvariant[n']
	some n, n' : Nicebook, c : Content, u : User | remove[n, n', u, c] and 
		userInvariant[n, u] and contentInvariant[n, c] and 
		nicebookInvariant[n] and nicebookInvariant[n']
	some n, n' : Nicebook, c : Content, u, u' : User, p : PrivacyLevel | 
		userInvariant[n, u] and userInvariant[n, u'] and 
			contentInvariant[n, c] and nicebookInvariant[n] and 
			publish[n, n', c, u, u', p] and nicebookInvariant[n']
	some n, n' : Nicebook, c : Content, u : User | 
		userInvariant[n, u] and contentInvariant[n, c] and nicebookInvariant[n] 
			and unpublish[n, n', c, u] and nicebookInvariant[n']
	some n, n' : Nicebook, u: User, c : Content, com, com' : Comment | 
		addComment[n, n', u, c , com, com'] and userInvariant[n, u] and 
		contentInvariant[n, c] and nicebookInvariant[n] and nicebookInvariant[n'] and
			contentInvariant[n, com] and contentInvariant[n, com']
	some n, n' : Nicebook, t : Tag | 
		nicebookInvariant[n] and tagInvariant[n, t] and 
			addTag[n, n', t] and nicebookInvariant[n']
	some n, n' : Nicebook, t : Tag, u : User | 
		userInvariant[n, u] and nicebookInvariant[n] and tagInvariant[n, t]
			and removeTag[n,n', t,u] and nicebookInvariant[n']
} for 15 but exactly 8 Nicebook
