module Util.Typst (
  readTypstWithMetaDataFile,
  typstWithMetaDataFileToHTML,
  typstAndMetaDataToHTML,
) where

-- aeson
import Data.Aeson

-- base
import Control.Monad

-- pandoc
import Text.Pandoc
import Text.Pandoc.Readers.Markdown

-- shake
import Development.Shake
import Development.Shake.FilePath

-- slick
import Slick.Pandoc

-- text
import Data.Text ( Text, pack )

-- | Given a path to a meta data file, produce a reader for Typst.
readTypstWithMetaDataFile :: FilePath -> PandocReader Text
readTypstWithMetaDataFile metaDataFile =
  (Pandoc <$> (yamlToMeta def (Just metaDataFile) =<< readMetadataFile metaDataFile) <*>) . (fmap (\(Pandoc _ b) -> b) . readTypst def)

-- | Given a path to a meta data file and content, convert to HTML with meta data.
typstWithMetaDataFileToHTML :: FilePath -> Text -> Action Value
typstWithMetaDataFileToHTML metaDataFile = loadUsing (readTypstWithMetaDataFile metaDataFile) (writeHtml5String defaultHtml5Options)

-- | Given a base file path, convert a metadata file with the "yaml" extension and a content file with the "typ" to HTML with metadata.
typstAndMetaDataToHTML :: FilePath -> Action Value
typstAndMetaDataToHTML base = typstWithMetaDataFileToHTML (base -<.> "yaml") . pack =<< readFile' (base -<.> "typ")
